use std::fs;

use bumpalo::Bump;
use clap::Parser;

use ligare::checker;
use ligare::checker::context::{ConstraintTable, add_refine, empty_ctx, empty_table};
use ligare::core::eval::eval;
use ligare::core::pool::{StringPool, TermArena};
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
    table: ConstraintTable<'bump>,
    env: Vec<(&'bump str, &'bump Term<'bump>)>,
    arena: &'bump TermArena<'bump>,
}

fn main() {
    let cli = Cli::parse();

    let bump = Bump::new();
    let _pool = StringPool::new(&bump);
    let arena = TermArena::new(&bump);

    let mut st = CompState {
        table: empty_table(),
        env: vec![],
        arena: &arena,
    };

    for file in &cli.files {
        if let Err(e) = process_file(&mut st, &bump, file) {
            eprintln!("{}", e);
        }
    }

    if let Some(expr) = &cli.eval {
        match parse_expr_top(expr, &bump, &arena) {
            Err(err) => eprintln!("--eval parse error: {}", err),
            Ok(term) => {
                let resolved = subst_top_level(&arena, &st.env, term);
                match eval(&arena, resolved) {
                    Err(err) => eprintln!("--eval error: {}", err),
                    Ok(val) => println!("{}", pretty(val)),
                }
            }
        }
    }
}

fn process_file<'bump>(
    st: &mut CompState<'bump>,
    bump: &'bump Bump,
    file: &str,
) -> Result<(), String> {
    let content = fs::read_to_string(file).map_err(|e| format!("{}: {}", file, e))?;
    let tops = parse_program(&content, bump, st.arena)
        .map_err(|e| format!("{}: parse error: {}", file, e))?;
    for top in tops {
        process_top_level(st, top)?;
    }
    Ok(())
}

fn process_top_level<'bump>(st: &mut CompState<'bump>, top: TopLevel<'bump>) -> Result<(), String> {
    match top {
        TopLevel::TLDef(name, term) => match term {
            Term::Refine(_, parent, predicate) => {
                println!("[refinement] {}", name);
                st.table = add_refine(name, parent, predicate, &st.table);
            }
            _ => {
                println!("[defined] {}", name);
                st.env.push((name, term));
            }
        },
        TopLevel::TLCheck(term, constraint) => {
            let resolved = subst_top_level(st.arena, &st.env, term);
            let resolved_constraint = subst_top_level(st.arena, &st.env, constraint);
            match checker::check(
                st.arena,
                &st.table,
                &empty_ctx(),
                resolved,
                resolved_constraint,
            ) {
                Err(err) => eprintln!("check failed: {}", err),
                Ok(_) => println!("[OK]"),
            }
        }
        TopLevel::TLExpr(term) => {
            let resolved = subst_top_level(st.arena, &st.env, term);
            match eval(st.arena, resolved) {
                Err(err) => eprintln!("eval error: {}", err),
                Ok(val) => println!("{}", pretty(val)),
            }
        }
    }
    Ok(())
}

/// Substitute known top-level definitions into a term.
fn subst_top_level<'bump>(
    arena: &TermArena<'bump>,
    env: &[(&'bump str, &'bump Term<'bump>)],
    term: &'bump Term<'bump>,
) -> &'bump Term<'bump> {
    match term {
        Term::Builtin(name) => {
            if let Some((_, body)) = env.iter().find(|(n, _)| *n == *name) {
                body
            } else {
                term
            }
        }
        Term::App(f, a) => {
            let f2 = subst_top_level(arena, env, f);
            let a2 = subst_top_level(arena, env, a);
            arena.app(f2, a2)
        }
        Term::Lam(body) => {
            let b2 = subst_top_level(arena, env, body);
            arena.lam(b2)
        }
        Term::Pi(n, a, b) => {
            let a2 = subst_top_level(arena, env, a);
            let b2 = subst_top_level(arena, env, b);
            arena.pi(n, a2, b2)
        }
        Term::Let(n, v, b, mc) => {
            let v2 = subst_top_level(arena, env, v);
            let b2 = subst_top_level(arena, env, b);
            let mc2 = mc.map(|c| subst_top_level(arena, env, c));
            arena.let_(n, v2, b2, mc2)
        }
        Term::IfThenElse(c, t, f) => {
            let c2 = subst_top_level(arena, env, c);
            let t2 = subst_top_level(arena, env, t);
            let f2 = subst_top_level(arena, env, f);
            arena.if_then_else(c2, t2, f2)
        }
        Term::Annot(t, c) => {
            let t2 = subst_top_level(arena, env, t);
            let c2 = subst_top_level(arena, env, c);
            arena.annot(t2, c2)
        }
        Term::ByProof(t, p) => {
            let t2 = subst_top_level(arena, env, t);
            let p2 = subst_top_level(arena, env, p);
            arena.by_proof(t2, p2)
        }
        Term::Refine(n, par, p) => {
            let par2 = subst_top_level(arena, env, par);
            let p2 = subst_top_level(arena, env, p);
            arena.refine(n, par2, p2)
        }
        Term::ProofBlock(t) => {
            let t2 = subst_top_level(arena, env, t);
            arena.proof_block(t2)
        }
        // Leaf nodes
        _ => term,
    }
}
