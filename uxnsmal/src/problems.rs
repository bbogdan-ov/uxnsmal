use crate::{error::Error, warn::Warn};

/// Problems.
#[derive(Default, Debug)]
pub struct Problems {
	pub errors: Vec<Error>,
	pub warns: Vec<Warn>,
}
impl Problems {
	pub fn one_err(error: Error) -> Self {
		Self {
			errors: vec![error],
			warns: Vec::default(),
		}
	}

	/// Push an error is any.
	pub fn err_or_ok<T>(&mut self, result: Result<T, Error>) {
		if let Err(e) = result {
			self.err(e);
		}
	}

	/// Push an error.
	pub fn err(&mut self, error: Error) {
		self.errors.push(error);
	}
	/// Push a warning.
	pub fn warn(&mut self, warn: Warn) {
		self.warns.push(warn);
	}
}
