mod lit;

use std::{
    collections::{HashMap, VecDeque},
    fmt::{Display, Formatter, Result},
};

use crate::lit::LBool;
pub use lit::Lit;
type Callback = Box<dyn Fn(&Engine, usize)>;

#[derive(Default)]
pub struct Engine {
    assigns: Vec<LBool>,                      // Current assignments of variables
    reason: Vec<Option<usize>>,               // Reason for each variable's assignment (index of the clause that caused the assignment)
    pos_watches: Vec<Vec<usize>>,             // Clauses watching the positive literal of each variable
    neg_watches: Vec<Vec<usize>>,             // Clauses watching the negative literal of each variable
    clauses: Vec<Vec<Lit>>,                   // List of clauses in the engine
    prop_q: VecDeque<usize>,                  // Queue of variables to propagate
    listeners: HashMap<usize, Vec<Callback>>, // Listeners for variable assignments
}

impl Engine {
    pub fn new() -> Self {
        Engine::default()
    }

    pub fn add_var(&mut self) -> usize {
        let var_id = self.assigns.len();
        self.assigns.push(LBool::Undef);
        self.reason.push(None);
        self.pos_watches.push(Vec::new());
        self.neg_watches.push(Vec::new());
        var_id
    }

    pub fn value(&self, var: usize) -> &LBool {
        &self.assigns[var]
    }

    pub fn lit_value(&self, lit: &Lit) -> LBool {
        match self.value(lit.var()) {
            LBool::True => {
                if lit.is_positive() {
                    LBool::True
                } else {
                    LBool::False
                }
            }
            LBool::False => {
                if lit.is_positive() {
                    LBool::False
                } else {
                    LBool::True
                }
            }
            LBool::Undef => LBool::Undef,
        }
    }

    pub fn add_listener<F>(&mut self, var: usize, listener: F)
    where
        F: Fn(&Engine, usize) + 'static,
    {
        self.listeners.entry(var).or_default().push(Box::new(listener));
    }
}

impl Display for Engine {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        for (i, val) in self.assigns.iter().enumerate() {
            writeln!(f, "b{}: {:?}", i, val)?;
        }
        for clause in &self.clauses {
            let lits: Vec<String> = clause.iter().map(|l| l.to_string()).collect();
            writeln!(f, "{}", lits.join(" ∨ "))?;
        }
        Ok(())
    }
}
