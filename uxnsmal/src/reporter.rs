use std::{
	fmt::{Display, Formatter},
	path::Path,
};

use crate::{
	error::{Error, StackError},
	lexer::{Span, Spanned},
};

// TODO: add "compact" mode for error reporting (usefull for VIM's quickfix)

const ESC: &str = "\x1b[";
const GRAY: &str = "\x1b[37m";
const BRED: &str = "\x1b[91m";
const BCYAN: &str = "\x1b[96m";
const RESET: &str = "\x1b[0m";

/// Error reporter
/// Writes a pretty printed error message with fancy things
pub struct Reporter<'a> {
	error: &'a Error,
	source: &'a str,
	filepath: &'a Path,
}
impl<'a> Reporter<'a> {
	pub fn new(error: &'a Error, source: &'a str, filepath: &'a Path) -> Self {
		Self {
			error,
			source,
			filepath,
		}
	}
}
impl<'a> Display for Reporter<'a> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		ReporterFmt::new(f, self).finish()
	}
}

/// Reporter formatter
struct ReporterFmt<'a, 'fmt> {
	fmt: &'a mut Formatter<'fmt>,
	rep: &'a Reporter<'a>,
}
impl<'a, 'fmt> ReporterFmt<'a, 'fmt> {
	fn new(fmt: &'a mut Formatter<'fmt>, rep: &'a Reporter<'a>) -> Self {
		Self { fmt, rep }
	}

	fn finish(mut self) -> std::fmt::Result {
		// Write error
		writeln!(self.fmt, "{BRED}error{RESET}: {}", self.rep.error)?;
		// Write filename and line where the error has occurred
		if let Some(span) = self.rep.error.span() {
			writeln!(self.fmt, "       at {}:{span}", self.rep.filepath.display())?;
		} else {
			writeln!(self.fmt, "       at {}", self.rep.filepath.display())?;
		}
		writeln!(self.fmt)?;

		// Write source code sample with underlined lines
		match self.rep.error {
			Error::InvalidStack {
				expected, stack, ..
			} => {
				writeln!(self.fmt, "expected: {expected:?}")?;
				self.write_stack_error(stack)?;
			}
			Error::InvalidIntrStack {
				expected, stack, ..
			} => {
				writeln!(self.fmt, "expected: {expected:?}")?;
				self.write_stack_error(stack)?;
			}
			Error::InvalidArithmeticStack { stack, .. }
			| Error::InvalidConditionType { stack, .. } => {
				writeln!(self.fmt, "expected: ( byte )")?;
				self.write_stack_error(stack)?;
			}

			Error::UnmatchedInputsSizes { found, .. } => {
				let hints = found
					.iter()
					.map(|s| Spanned::new(format!("size is {} bytes", s.x), s.span))
					.collect();

				self.write_source(hints)?;
			}
			Error::UnmatchedInputsTypes { found, .. } => {
				let hints = found
					.iter()
					.map(|t| Spanned::new(format!("this is '{}'", t.typ), t.pushed_at))
					.collect();

				self.write_source(hints)?;
			}
			Error::UnmatchedNames {
				found, expected, ..
			} => {
				let hints = found
					.iter()
					.map(|s| match &s.x {
						Some(name) => Spanned::new(format!("name is `{}`", name), s.span),
						None => Spanned::new("no name".into(), s.span),
					})
					.collect();

				writeln!(self.fmt, "expected: {expected:?}")?;
				writeln!(self.fmt, "   found: {found:?}")?;
				writeln!(self.fmt)?;

				self.write_source(hints)?;
			}

			Error::IllegalVectorCall { defined_at, .. }
			| Error::SymbolRedefinition { defined_at, .. }
			| Error::LabelRedefinition { defined_at, .. } => {
				let hints = vec![Spanned::new("defined here".into(), *defined_at)];
				self.write_source(hints)?
			}

			_ => self.write_source(vec![])?,
		}

		Ok(())
	}

	fn write_stack_error(&mut self, error: &StackError) -> std::fmt::Result {
		match error {
			StackError::Invalid { found } => {
				writeln!(self.fmt, "   found: {found:?}")?;
				writeln!(self.fmt)?;
				self.write_source(vec![])?;
			}
			StackError::TooFew { found, consumed_by } => {
				writeln!(self.fmt, "   found: {found:?}")?;
				writeln!(self.fmt)?;

				let hints = consumed_by
					.iter()
					.map(|s| Spanned::new("consumed here".into(), *s))
					.collect();

				self.write_source(hints)?;
			}
			StackError::TooMany { found, caused_by } => {
				writeln!(self.fmt, "   found: {found:?}")?;
				writeln!(self.fmt)?;

				let hints = caused_by
					.iter()
					.map(|s| Spanned::new("caused by this".into(), *s))
					.collect();

				self.write_source(hints)?;
			}
		}
		Ok(())
	}

	fn write_source(&mut self, hints: Vec<Spanned<String>>) -> std::fmt::Result {
		let Some(err_span) = self.rep.error.span() else {
			return Ok(());
		};

		let mut last_idx: Option<usize> = None;

		let iter = self.rep.source.lines().enumerate();
		for (line_idx, line) in iter {
			if !self.should_be_reported(line_idx, err_span, &hints) {
				continue;
			}

			// If line number difference between last line and the current
			// one is more than 1, write "..."
			if last_idx.is_some_and(|i| line_idx - i > 1) {
				writeln!(self.fmt, "{GRAY}   ...{RESET}")?;
			}

			self.write_line(line_idx, line, err_span, &hints)?;
			last_idx = Some(line_idx);
		}

		writeln!(self.fmt)
	}
	fn write_line(
		&mut self,
		line_idx: usize,
		line: &str,
		err_span: Span,
		hints: &[Spanned<String>],
	) -> std::fmt::Result {
		// TODO: it may overlap with the underline if there are one or more tabs in the line
		// Example:
		// fun error-is-here ( -- ) {
		//     do-this^^^^^^ <- overlap because \t is rendered as 4 chars,
		// }                    but it still counts as one char

		// Write line number
		let line_num = line_idx + 1;
		self.write_line_num(line_num)?;

		// Write each line character
		for ch in line.chars() {
			if ch == '\t' {
				write!(self.fmt, "    ")?;
			} else {
				write!(self.fmt, "{ch}")?;
			}
		}
		writeln!(self.fmt)?;

		// Underline error span
		if line_idx == err_span.line {
			self.write_underline(BRED, line, "", err_span)?;
		}

		for hint in hints {
			if hint.span.line == line_idx {
				self.write_underline(BCYAN, line, &hint.x, hint.span)?;
			}
		}

		Ok(())
	}

	fn write_underline(
		&mut self,
		color: &str,
		line: &str,
		msg: &str,
		span: Span,
	) -> std::fmt::Result {
		let range = span.range_on_line(line);
		self.write_line_num("")?;

		if range.start > 0 {
			write!(self.fmt, "{ESC}{}C", range.start)?; // move cursor right
		}
		write!(self.fmt, "{color}{}", "^".repeat(range.len() + 1))?; // write underline ^^^

		writeln!(self.fmt, " {msg}")?;

		Ok(())
	}
	fn write_line_num(&mut self, text: impl Display) -> std::fmt::Result {
		write!(self.fmt, "{GRAY}")?;
		write!(self.fmt, "{text:>4}")?;
		write!(self.fmt, " | {RESET}")
	}

	/// Returns whether the line have something to be reported
	fn should_be_reported(
		&self,
		line_idx: usize,
		err_span: Span,
		hints: &[Spanned<String>],
	) -> bool {
		let range = err_span.line.saturating_sub(1)..=err_span.line + 1;
		hints.iter().any(|s| s.span.line == line_idx) || range.contains(&line_idx)
	}
}
