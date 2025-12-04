use std::{
	fmt::{Display, Formatter},
	path::Path,
};

use crate::{
	error::{Error, Hint},
	lexer::Span,
	problems::Problems,
	warn::Warn,
};

// TODO: add "compact" mode for error reporting (usefull for VIM's quickfix)

// TODO: add "no color" mode which will disable all esapce sequences in error reports.
// This mode also should be enabled automatically when piping output somewhere else.

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
				expected, found, ..
			} => {
				writeln!(self.fmt, "expected: {expected:?}")?;
				writeln!(self.fmt, "   found: {found:?}")?;
				writeln!(self.fmt)?;
			}

			Error::UnmatchedNames {
				found, expected, ..
			} => {
				writeln!(self.fmt, "expected: {expected:?}")?;
				writeln!(self.fmt, "   found: {found:?}")?;
				writeln!(self.fmt)?;
			}

			_ => (),
		}

		if let Some(err_span) = error.span() {
			let mut hints = error.hints();
			hints.reverse();
			self.write_source(BRED, err_span, &hints)?;
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
			self.write_source(BYELLOW, span, &[])?;
		}

		write!(self.fmt, "{RESET}")?;

		Ok(())
	}

	fn write_source(
		&mut self,
		err_color: &'static str,
		err_span: Span,
		hints: &[Hint],
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
		hints: &[Hint],
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
			self.write_underline::<&str>(err_color, line, None, err_span)?;
		}

		for hint in hints {
			if hint.span.line == line_idx {
				self.write_underline(BCYAN, line, Some(&hint.kind), hint.span)?;
			}
		}

		Ok(())
	}

	fn write_underline<M: Display>(
		&mut self,
		color: &str,
		line: &str,
		msg: Option<&M>,
		span: Span,
	) -> std::fmt::Result {
		let range = span.range_on_line(line);
		self.write_line_num("")?;

		if range.start > 0 {
			write!(self.fmt, "{ESC}{}C", range.start)?; // move cursor right
		}
		write!(self.fmt, "{color}{}", "^".repeat(range.len() + 1))?; // write underline ^^^

		match msg {
			Some(msg) => writeln!(self.fmt, " {}", msg)?,
			None => writeln!(self.fmt)?,
		}

		Ok(())
	}
	fn write_line_num(&mut self, text: impl Display) -> std::fmt::Result {
		write!(self.fmt, "{GRAY}")?;
		write!(self.fmt, "{text:>4}")?;
		write!(self.fmt, " | {RESET}")
	}

	/// Returns whether the line have something to be reported
	fn should_be_reported(&self, line_idx: usize, err_span: Span, hints: &[Hint]) -> bool {
		let range = err_span.line.saturating_sub(1)..=err_span.line + 1;
		hints.iter().any(|s| s.span.line == line_idx) || range.contains(&line_idx)
	}
}
