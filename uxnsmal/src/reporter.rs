use std::{
	fmt::{Display, Formatter},
	path::Path,
};

use crate::{
	lexer::Span,
	problem::{ProblemKind, Problems},
};

// TODO: add "compact" mode for error reporting (usefull for VIM's quickfix).

// TODO: add "no color" mode which will disable all esapce sequences in error reports.
// This mode also should be enabled automatically when piping output somewhere else.

// FIXME: properly underline non-ascii characters.
// Currently `Reporter` counts each char as a byte which is not correct.

const ESC: &str = "\x1b[";
const GRAY: &str = "\x1b[37m";
const BRED: &str = "\x1b[91m";
const BYELLOW: &str = "\x1b[93m";
const BCYAN: &str = "\x1b[96m";
const RESET: &str = "\x1b[0m";

/// Error reporter.
/// Writes a pretty printed error message with fancy things.
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

		for problem in self.problems.list.iter() {
			let (color, label) = match problem.kind {
				ProblemKind::Error => (BRED, "error"),
				ProblemKind::Warning => (BYELLOW, "warning"),
			};

			fmt.write_problem(color, label, &problem.msg, problem.span)?;
			for note in problem.notes.iter() {
				fmt.write_problem(BCYAN, "note", &note.msg, note.span)?;
			}

			writeln!(fmt.fmt)?;
		}

		Ok(())
	}
}

/// Reporter formatter.
struct ReporterFmt<'a, 'fmt> {
	fmt: &'a mut Formatter<'fmt>,
	rep: &'a Reporter<'a>,
}
impl<'a, 'fmt> ReporterFmt<'a, 'fmt> {
	fn new(fmt: &'a mut Formatter<'fmt>, rep: &'a Reporter<'a>) -> Self {
		Self { fmt, rep }
	}

	fn write_problem(
		&mut self,
		color: &str,
		label: &str,
		msg: &str,
		span: Span,
	) -> std::fmt::Result {
		// Write filename and line .
		write!(self.fmt, "{}:{}: ", self.rep.filepath.display(), span)?;
		// Write problem message.
		writeln!(self.fmt, "{color}{label}{RESET}: {}", msg)?;

		// Write source code sample.
		self.write_source(color, span)?;

		write!(self.fmt, "{RESET}")?;
		Ok(())
	}

	fn write_source(&mut self, color: &str, err_span: Span) -> std::fmt::Result {
		let line = self
			.rep
			.source
			.lines()
			.nth(err_span.line)
			.expect("TODO: properly handle Option");

		self.write_line(line, err_span, color)
	}
	fn write_line(&mut self, line: &str, err_span: Span, color: &str) -> std::fmt::Result {
		// Write line number.
		let line_num = err_span.line + 1;
		self.write_line_num(line_num)?;

		let trimmed = line.trim();
		writeln!(self.fmt, "{}", trimmed)?;

		// Underline error span.
		self.write_underline(color, line, err_span)?;

		Ok(())
	}

	fn write_underline(&mut self, color: &str, line: &str, span: Span) -> std::fmt::Result {
		let mut offset = 0;
		for ch in line.chars() {
			if ch == '\t' {
				offset += 4;
			} else if ch.is_whitespace() {
				offset += 1;
			} else {
				break;
			}
		}

		let mut range = span.range_on_line(line);
		range.start = range.start.saturating_sub(offset);
		range.end = range.end.saturating_sub(offset);
		self.write_line_num("")?;

		if range.start > 0 {
			write!(self.fmt, "{ESC}{}C", range.start)?; // move cursor right
		}
		writeln!(self.fmt, "{color}{}", "^".repeat(range.len() + 1))?; // write underline ^^^

		Ok(())
	}
	fn write_line_num(&mut self, text: impl Display) -> std::fmt::Result {
		write!(self.fmt, "{GRAY}{text:>4}| {RESET}")
	}
}
