use std::{
	fmt::{Display, Formatter, Write},
	path::Path,
};

use crate::{
	error::{Error, ErrorKind, HintKind},
	lexer::Span,
	program::Type,
	typechecker::StackMatch,
};

const ESC: &str = "\x1b[";
const CYAN: &str = "\x1b[36m";
const GRAY: &str = "\x1b[37m";
const BRED: &str = "\x1b[91m";
const RESET: &str = "\x1b[0m";

const CURSOR_UP: &str = "\x1b[1A";
const CURSOR_DOWN: &str = "\x1b[1B";
const CURSOR_LEFT: &str = "\x1b[1D";

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

	prev_underline_span: Option<(Span, u8, Option<HintKind>)>,
}
impl<'a, 'fmt> ReporterFmt<'a, 'fmt> {
	fn new(fmt: &'a mut Formatter<'fmt>, rep: &'a Reporter<'a>) -> Self {
		Self {
			fmt,
			rep,

			prev_underline_span: None,
		}
	}

	fn finish(mut self) -> std::fmt::Result {
		// Write error
		writeln!(self.fmt, "{BRED}error{RESET}: {}", self.rep.error.kind)?;
		// Write filename and line where the error has occurred
		if let Some(span) = self.rep.error.span {
			writeln!(
				self.fmt,
				"       in {} at {span}",
				self.rep.filepath.display(),
			)?;
		} else {
			writeln!(self.fmt, "       in {}", self.rep.filepath.display())?;
		}
		writeln!(self.fmt)?;

		// Write expected and found stacks
		if let Some(stacks) = &self.rep.error.stacks {
			let mut found_buf = String::with_capacity(64);
			let mut expected_buf = String::with_capacity(64);

			let is_tail = stacks.mtch == StackMatch::Tail;

			let found_width = self.render_stack(&mut found_buf, &stacks.found, is_tail)?;
			let expected_width = self.render_stack(&mut expected_buf, &stacks.expected, is_tail)?;
			let max_width = found_width.max(expected_width);

			write!(self.fmt, "{CYAN}expected{RESET}: ")?;
			if is_tail {
				let pad = max_width.saturating_sub(expected_width);
				write!(self.fmt, "{}", " ".repeat(pad))?;
			}
			write!(self.fmt, "{expected_buf}",)?;

			write!(self.fmt, "{CYAN}   found{RESET}: ")?;
			if is_tail {
				let pad = max_width.saturating_sub(found_width);
				write!(self.fmt, "{}", " ".repeat(pad))?;
			}
			write!(self.fmt, "{found_buf}",)?;
			writeln!(self.fmt)?;
		}

		if let ErrorKind::IntrinsicInvalidStackHeight { expected, found } = &self.rep.error.kind {
			writeln!(
				self.fmt,
				"{CYAN}expected at least{RESET} {expected} {CYAN}but found{RESET} {found}"
			)?;
			writeln!(self.fmt)?;
		}

		// Write source code sample with underlined lines
		self.write_source()?;

		Ok(())
	}

	/// Render stack signature onto a buffer (string or something)
	fn render_stack(
		&mut self,
		buf: &mut impl Write,
		stack: &[Type],
		tail: bool,
	) -> Result<usize, std::fmt::Error> {
		let mut width = 0;

		if stack.is_empty() {
			write!(buf, "{GRAY}empty{RESET}")?;
			width += 5;
		} else {
			write!(buf, "( ")?;
			width += 2;

			if tail {
				write!(buf, ".. ")?;
				width += 3;
			}

			for (idx, typ) in stack.iter().enumerate() {
				let typ_str = typ.to_string();
				write!(buf, "{typ_str}")?;
				width += typ_str.len();

				if idx < stack.len() - 1 {
					write!(buf, ", ")?;
					width += 2;
				}
			}
			write!(buf, " )")?;
			width += 2;
		}

		writeln!(buf)?;

		Ok(width)
	}

	fn write_source(&mut self) -> std::fmt::Result {
		let Some(err_span) = self.rep.error.span else {
			return Ok(());
		};

		let mut last_idx: Option<usize> = None;

		let iter = self.rep.source.lines().enumerate();
		for (line_idx, line) in iter {
			if !self.should_be_reported(line_idx, err_span) {
				continue;
			}

			// If line number difference between last line and the current
			// one is more than 1, write "..."
			if last_idx.is_some_and(|i| line_idx - i > 1) {
				writeln!(self.fmt, "{GRAY}   ...{RESET}")?;
				self.prev_underline_span = None;
			}

			self.write_line(line_idx, line, err_span)?;
			last_idx = Some(line_idx);
		}

		writeln!(self.fmt)
	}
	fn write_line(&mut self, line_idx: usize, line: &str, err_span: Span) -> std::fmt::Result {
		// Move the line up if it will not overlap previous underline
		if let Some((underline_span, _, _)) = self.prev_underline_span.take() {
			if line.len() <= underline_span.col {
				write!(self.fmt, "{CURSOR_UP}")?;
			}
		}

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
			self.write_underline(BRED, line, err_span, None)?;
		}

		// Underline hint span
		for hint in self.rep.error.hints.list().iter() {
			if line_idx == hint.span.line {
				self.write_underline(CYAN, line, hint.span, Some(hint.kind.clone()))?;
			}
		}

		Ok(())
	}

	fn write_underline(
		&mut self,
		color: &str,
		line: &str,
		span: Span,
		hint_kind: Option<HintKind>,
	) -> std::fmt::Result {
		let range = span.range_on_line(line);
		let mut depth = 0;
		let mut repeated = false;

		// Move this underline up if it will not overlap previous underline
		if let Some((underline_span, prev_depth, prev_hint)) = &self.prev_underline_span {
			repeated = *prev_hint == hint_kind;

			if underline_span.end < span.start {
				write!(self.fmt, "{CURSOR_UP}")?;
			} else if underline_span.start > span.end {
				depth = *prev_depth;
			}
		}
		if repeated {
			depth = 1;
		}

		self.write_line_num("")?;

		if range.start > 0 {
			write!(self.fmt, "{ESC}{}C", range.start)?; // move cursor right
		}
		if depth > 0 {
			write!(self.fmt, "{ESC}{depth}A")?; // move cursor up
		}
		write!(self.fmt, "{color}{}", "^".repeat(range.len() + 1))?; // write underline ^^^

		if !repeated && let Some(hint_kind) = &hint_kind {
			for _ in 0..depth {
				write!(self.fmt, "{CURSOR_DOWN}{CURSOR_LEFT}|")?;
			}
			write!(self.fmt, " {hint_kind}{RESET}",)?;
		}

		writeln!(self.fmt)?;

		self.prev_underline_span = Some((span, depth + 1, hint_kind));

		Ok(())
	}
	fn write_line_num(&mut self, text: impl Display) -> std::fmt::Result {
		write!(self.fmt, "{GRAY}")?;
		write!(self.fmt, "{text:>4}")?;
		write!(self.fmt, " | {RESET}")
	}

	/// Returns whether the line have something to be reported
	fn should_be_reported(&self, line_idx: usize, err_span: Span) -> bool {
		let mut hints = self.rep.error.hints.list().iter();
		let range = err_span.line.saturating_sub(1)..=err_span.line + 1;

		hints.any(|h| h.span.line == line_idx) || range.contains(&line_idx)
	}
}
