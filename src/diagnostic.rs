/// A source span: byte offset range in the source text.
pub type Span = std::ops::Range<usize>;

/// A structured diagnostic message with optional source span information.
///
/// Replaces bare `String` errors in public-facing compiler APIs so callers
/// can highlight the relevant source location without parsing error messages.
#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub message: String,
    pub span: Option<Span>,
}

impl Diagnostic {
    /// Create a diagnostic with just a message (no span).
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            span: None,
        }
    }

    /// Create a diagnostic with both a message and a source span.
    pub fn with_span(message: impl Into<String>, span: Span) -> Self {
        Self {
            message: message.into(),
            span: Some(span),
        }
    }
}

impl std::fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(span) = &self.span {
            write!(f, "{} (at {}..{})", self.message, span.start, span.end)
        } else {
            write!(f, "{}", self.message)
        }
    }
}

impl std::error::Error for Diagnostic {}
