//! Positions inside a term. Ported from `lib/adamas/path.rb`.
//!
//! Descending into an abstraction *opens* it, so the subterm at a position is
//! always a closed term rather than something with a dangling index. That is
//! what makes a position under a binder matchable and rewritable at all.
//!
//! The variable it is opened with comes from the *position* — `_0` for the
//! outermost binder on the path, `_1` for the next — and deliberately not from
//! `dest_abs`, which names it after the binder's display name. A display name
//! is whichever alpha-variant happened to be interned first in this process,
//! and a certificate has to mean the same thing in the process that replays it
//! as in the one that wrote it. Naming from the position makes a certificate
//! portable; naming from the binder would have made it a local accident.

use crate::kernel::{Error, Kernel, Result, Term, TermNode};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum PathStep {
    Rator,
    Rand,
    Body,
}

impl std::fmt::Display for PathStep {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PathStep::Rator => write!(f, "rator"),
            PathStep::Rand => write!(f, "rand"),
            PathStep::Body => write!(f, "body"),
        }
    }
}

pub fn path_to_string(path: &[PathStep]) -> String {
    if path.is_empty() {
        "the whole term".to_string()
    } else {
        path.iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>()
            .join(".")
    }
}

impl Kernel {
    /// The variable used to open an abstraction found at `depth` binders down a
    /// path. Primed if the term already has a free variable of that name, so it
    /// is always fresh and the abstraction can be rebuilt from it exactly.
    pub fn path_opener(&mut self, abs: Term, depth: usize) -> Result<Term> {
        let TermNode::Abs { binder_type, .. } = self.term_node(abs).clone() else {
            return Err(Error::Path(format!(
                "cannot take body of {}",
                self.term_to_string(abs)
            )));
        };
        let avoid = self.frees(abs).to_vec();
        self.variant(&avoid, &format!("_{depth}"), binder_type)
    }

    pub fn open_body(&mut self, abs: Term, depth: usize) -> Result<Term> {
        let opener = self.path_opener(abs, depth)?;
        self.open_abs(abs, opener)
    }

    pub fn subterm(&mut self, term: Term, path: &[PathStep]) -> Result<Term> {
        self.subterm_at(term, path, 0)
    }

    fn subterm_at(&mut self, term: Term, path: &[PathStep], depth: usize) -> Result<Term> {
        let Some((step, rest)) = path.split_first() else {
            return Ok(term);
        };
        match (step, self.term_node(term).clone()) {
            (PathStep::Rator, TermNode::Comb { rator, .. }) => self.subterm_at(rator, rest, depth),
            (PathStep::Rand, TermNode::Comb { rand, .. }) => self.subterm_at(rand, rest, depth),
            (PathStep::Body, TermNode::Abs { .. }) => {
                let body = self.open_body(term, depth)?;
                self.subterm_at(body, rest, depth + 1)
            }
            _ => Err(Error::Path(format!(
                "cannot take {step} of {}",
                self.term_to_string(term)
            ))),
        }
    }

    /// `term` with the subterm at `path` replaced. Rebuilt through the ordinary
    /// constructors, so the result is type-checked like anything else.
    pub fn replace(&mut self, term: Term, path: &[PathStep], replacement: Term) -> Result<Term> {
        self.replace_at(term, path, replacement, 0)
    }

    fn replace_at(
        &mut self,
        term: Term,
        path: &[PathStep],
        replacement: Term,
        depth: usize,
    ) -> Result<Term> {
        let Some((step, rest)) = path.split_first() else {
            return Ok(replacement);
        };
        match (step, self.term_node(term).clone()) {
            (PathStep::Rator, TermNode::Comb { rator, rand }) => {
                let new_rator = self.replace_at(rator, rest, replacement, depth)?;
                self.term_comb(new_rator, rand)
            }
            (PathStep::Rand, TermNode::Comb { rator, rand }) => {
                let new_rand = self.replace_at(rand, rest, replacement, depth)?;
                self.term_comb(rator, new_rand)
            }
            (PathStep::Body, TermNode::Abs { binder_name, .. }) => {
                // Rebuilt under the binder's own display name: `_0` is a working
                // variable for naming the position, not something a reader
                // should meet in the rewritten term.
                let var = self.path_opener(term, depth)?;
                let opened = self.open_abs(term, var)?;
                let body = self.replace_at(opened, rest, replacement, depth + 1)?;
                self.term_abs_named(&binder_name, var, body)
            }
            _ => Err(Error::Path(format!(
                "cannot take {step} of {}",
                self.term_to_string(term)
            ))),
        }
    }

    /// Every position in `term`, outermost first and left to right.
    pub fn positions(&mut self, term: Term) -> Result<Vec<(Vec<PathStep>, Term)>> {
        let mut out = Vec::new();
        self.walk(term, &mut Vec::new(), 0, &mut out)?;
        Ok(out)
    }

    fn walk(
        &mut self,
        term: Term,
        path: &mut Vec<PathStep>,
        depth: usize,
        out: &mut Vec<(Vec<PathStep>, Term)>,
    ) -> Result<()> {
        out.push((path.clone(), term));
        match self.term_node(term).clone() {
            TermNode::Comb { rator, rand } => {
                path.push(PathStep::Rator);
                self.walk(rator, path, depth, out)?;
                path.pop();
                path.push(PathStep::Rand);
                self.walk(rand, path, depth, out)?;
                path.pop();
            }
            TermNode::Abs { .. } => {
                let body = self.open_body(term, depth)?;
                path.push(PathStep::Body);
                self.walk(body, path, depth + 1, out)?;
                path.pop();
            }
            _ => {}
        }
        Ok(())
    }
}
