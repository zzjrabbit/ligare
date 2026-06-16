use std::fs;

use bumpalo::Bump;
use clap::Parser;

use ligare::checker::checker;
use ligare::checker::context::{ConstraintTable, add_refine, empty_ctx, empty_table};
use ligare::core::eval::eval;
use ligare::core::pool::StringPool;
use ligare::core::syntax::Term;
use ligare::front::parser::{TopLevel, parse_expr_top, parse_program};
use ligare::pretty::pretty;

#[derive(Parser)]
#[command(
    name = "ligare",
    about = "Ligare compiler frontend",
    long_about = "Each source file may contain:\n  def <name> [params] [: <type>] := <body>   top-level definition\n  #check <term> : <constraint>               type-check assertion\n  <expr>                                      evaluate expression"
)]
struct Cli {
    /// Evaluate an expression after processing all files
    #[arg(long, value_name = "EXPR")]
    eval: Option<String>,

    /// Source files to process
    #[arg(required = true)]
    files: Vec<String>,
}

struct CompState<'bump> {
    table: ConstraintTable,
    env: Vec<(String, Term)>,
    #[allow(dead_code)]
    pool: &'bump StringPool<'bump>,
}

fn main() {
    let cli = Cli::parse();

    let bump = Bump::new();
    let pool = StringPool::new(&bump);

    let mut st = CompState {
        table: empty_table(),
        env: vec![],
        pool: &pool,
    };

    for file in &cli.files {
        let file_ref: &str = file;
        match process_file(&mut st, file_ref) {
            Ok(()) => {}
            Err(e) => eprintln!("{}", e),
        }
    }

    if let Some(expr) = &cli.eval {
        match parse_expr_top(expr) {
            Err(err) => eprintln!("--eval parse error: {}", err),
            Ok(term) => {
                let resolved = subst_top_level(&st.env, &term);
                match eval(&resolved) {
                    Err(err) => eprintln!("--eval error: {}", err),
                    Ok(val) => println!("{}", pretty(&val)),
                }
            }
        }
    }
}

fn process_file(st: &mut CompState<'_>, file: &str) -> Result<(), String> {
    let content = fs::read_to_string(file).map_err(|e| format!("{}: {}", file, e))?;
    let tops = parse_program(&content).map_err(|e| format!("{}: parse error: {}", file, e))?;
    for top in tops {
        process_top_level(st, top)?;
    }
    Ok(())
}

fn process_top_level(st: &mut CompState<'_>, top: TopLevel) -> Result<(), String> {
    match top {
        TopLevel::TLDef(name, term) => match &term {
            Term::Refine(_, parent, predicate) => {
                println!("[refinement] {}", name);
                st.table = add_refine(
                    name.clone(),
                    parent.as_ref().clone(),
                    predicate.as_ref().clone(),
                    &st.table,
                );
            }
            _ => {
                println!("[defined] {}", name);
                st.env.push((name, term));
            }
        },
        TopLevel::TLCheck(term, constraint) => {
            let resolved = subst_top_level(&st.env, &term);
            let resolved_constraint = subst_top_level(&st.env, &constraint);
            match checker::check(&st.table, &empty_ctx(), &resolved, &resolved_constraint) {
                Err(err) => eprintln!("check failed: {}", err),
                Ok(_) => println!("[OK]"),
            }
        }
        TopLevel::TLExpr(term) => {
            let resolved = subst_top_level(&st.env, &term);
            match eval(&resolved) {
                Err(err) => eprintln!("eval error: {}", err),
                Ok(val) => println!("{}", pretty(&val)),
            }
        }
    }
    Ok(())
}

/// Substitute known top-level definitions into a term.
fn subst_top_level(env: &[(String, Term)], term: &Term) -> Term {
    match term {
        Term::Builtin(name) => {
            if let Some((_, body)) = env.iter().find(|(n, _)| n == name) {
                body.clone()
            } else {
                term.clone()
            }
        }
        Term::App(f, a) => Term::App(
            Box::new(subst_top_level(env, f)),
            Box::new(subst_top_level(env, a)),
        ),
        Term::Lam(body) => Term::Lam(Box::new(subst_top_level(env, body))),
        Term::Pi(n, a, b) => Term::Pi(
            n.clone(),
            Box::new(subst_top_level(env, a)),
            Box::new(subst_top_level(env, b)),
        ),
        Term::Let(n, v, b, mc) => Term::Let(
            n.clone(),
            Box::new(subst_top_level(env, v)),
            Box::new(subst_top_level(env, b)),
            mc.as_ref().map(|c| Box::new(subst_top_level(env, c))),
        ),
        Term::IfThenElse(c, t, f) => Term::IfThenElse(
            Box::new(subst_top_level(env, c)),
            Box::new(subst_top_level(env, t)),
            Box::new(subst_top_level(env, f)),
        ),
        Term::Annot(t, c) => Term::Annot(
            Box::new(subst_top_level(env, t)),
            Box::new(subst_top_level(env, c)),
        ),
        Term::ByProof(t, p) => Term::ByProof(
            Box::new(subst_top_level(env, t)),
            Box::new(subst_top_level(env, p)),
        ),
        Term::Refine(n, par, p) => Term::Refine(
            n.clone(),
            Box::new(subst_top_level(env, par)),
            Box::new(subst_top_level(env, p)),
        ),
        Term::ProofBlock(t) => Term::ProofBlock(Box::new(subst_top_level(env, t))),
        Term::This => Term::This,
        other => other.clone(),
    }
}
