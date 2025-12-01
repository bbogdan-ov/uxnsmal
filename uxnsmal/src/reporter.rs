use std::{
	fmt::{Display, Formatter},
	path::Path,
};

use crate::{
	error::{Error, StackError},
	lexer::{Span, Spanned},
	problems::Problems,
	warn::Warn,
};

// TODO: add "compact" mode for error reporting (usefull for VIM's quickfix)

const ESC: &str = "\x1b[";
const GRAY: &str = "\x1b[37m";
const BRED: &str = "\x1b[91m";
const BYELLOW: &str = "\x1b[93m";
const BCYAN: &str = "\x1b[96m";
const RESET: &str = "\x1b[0m";

/// Error reporter
/// Writes a pretty printed error message with fancy things
pub struct Reporter<'a> {
	problems: &'a Problems,
	source: &'a str,
	filepath: &'a Path,
}
impl<'a> Reporter<'a> {
	pub fn new(problems: &'a Problems, source: &'a str, filepath: &'a Path) -> Self {
		Self {
			problems,
			source,
			filepath,
		}
	}
}
impl<'a> Display for Reporter<'a> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		let mut fmt = ReporterFmt::new(f, self);

		for warn in self.problems.warns.iter() {
			fmt.write_warn(warn)?;
		}
		for err in self.problems.errors.iter() {
			fmt.write_error(err)?;
		}

		Ok(())
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

	fn write_error(&mut self, error: &Error) -> std::fmt::Result {
		writeln!(self.fmt)?;

		// Write filename and line where the error has occurred
		if let Some(span) = error.span() {
			write!(self.fmt, "{}:{span}: ", self.rep.filepath.display())?;
		} else {
			write!(self.fmt, "{}: ", self.rep.filepath.display())?;
		}
		// Write error message
		writeln!(self.fmt, "{BRED}error{RESET}: {}", error)?;
		writeln!(self.fmt)?;

		// Write source code sample with underlined lines
		match error {
			Error::InvalidStack {
				expected,
				found,
				stack,
				span,
			} => {
				writeln!(self.fmt, "expected: {expected:?}")?;
				writeln!(self.fmt, "   found: {found:?}")?;
				self.write_stack_error(BRED, *span, stack)?;
			}
			Error::InvalidIntrStack {
				expected,
				found,
				stack,
				span,
			} => {
				writeln!(self.fmt, "expected: {expected:?}")?;
				writeln!(self.fmt, "   found: {found:?}")?;
				self.write_stack_error(BRED, *span, stack)?;
			}
			Error::InvalidArithmeticStack { found, stack, span }
			| Error::InvalidConditionType { found, stack, span } => {
				writeln!(self.fmt, "expected: ( byte )")?;
				writeln!(self.fmt, "   found: {found:?}")?;
				self.write_stack_error(BRED, *span, stack)?;
			}

			Error::UnmatchedInputsSizes { found, span } => {
				let hints = found
					.iter()
					.map(|s| Spanned::new(format!("size is {} bytes", s.x), s.span))
					.collect();

				self.write_source(BRED, *span, hints)?;
			}
			Error::UnmatchedInputsTypes { found, span } => {
				let hints = found
					.iter()
					.map(|t| Spanned::new(format!("this is '{}'", t.typ), t.pushed_at))
					.collect();

				self.write_source(BRED, *span, hints)?;
			}
			Error::UnmatchedNames {
				found,
				expected,
				span,
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

				self.write_source(BRED, *span, hints)?;
			}

			Error::IllegalVectorCall { defined_at, span }
			| Error::SymbolRedefinition { defined_at, span }
			| Error::LabelRedefinition { defined_at, span }
			| Error::NotType { defined_at, span } => {
				let hints = vec![Spanned::new("defined here".into(), *defined_at)];
				self.write_source(BRED, *span, hints)?
			}

			e => {
				if let Some(span) = e.span() {
					self.write_source(BRED, span, vec![])?;
				}
			}
		}

		write!(self.fmt, "{RESET}")?;

		Ok(())
	}

	fn write_warn(&mut self, warn: &Warn) -> std::fmt::Result {
		writeln!(self.fmt)?;

		// Write filename and line where the error has occurred
		if let Some(span) = warn.span() {
			write!(self.fmt, "{}:{span}: ", self.rep.filepath.display())?;
		} else {
			write!(self.fmt, "{}: ", self.rep.filepath.display())?;
		}
		// Write warning message
		writeln!(self.fmt, "{BYELLOW}warning{RESET}: {}", warn)?;
		writeln!(self.fmt)?;

		if let Some(span) = warn.span() {
			self.write_source(BYELLOW, span, vec![])?;
		}

		write!(self.fmt, "{RESET}")?;

		Ok(())
	}

	fn write_stack_error(
		&mut self,
		err_color: &'static str,
		err_span: Span,
		error: &StackError,
	) -> std::fmt::Result {
		match error {
			StackError::Invalid => {
				writeln!(self.fmt)?;
				self.write_source(err_color, err_span, vec![])?;
			}
			StackError::TooFew { consumed_by } => {
				writeln!(self.fmt)?;

				let hints = consumed_by
					.iter()
					.map(|s| Spanned::new("consumed here".into(), *s))
					.collect();

				self.write_source(err_color, err_span, hints)?;
			}
			StackError::TooMany { caused_by } => {
				writeln!(self.fmt)?;

				let hints = caused_by
					.iter()
					.map(|s| Spanned::new("caused by this".into(), *s))
					.collect();

				self.write_source(err_color, err_span, hints)?;
			}
		}
		Ok(())
	}

	fn write_source(
		&mut self,
		err_color: &'static str,
		err_span: Span,
		hints: Vec<Spanned<String>>,
	) -> std::fmt::Result {
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

			self.write_line(line_idx, line, err_span, err_color, &hints)?;
			last_idx = Some(line_idx);
		}

		writeln!(self.fmt)
	}
	fn write_line(
		&mut self,
		line_idx: usize,
		line: &str,
		err_span: Span,
		err_color: &'static str,
		hints: &[Spanned<String>],
	) -> std::fmt::Result {
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
			self.write_underline(err_color, line, "", err_span)?;
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
