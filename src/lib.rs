mod lit;

use std::{
    collections::{HashMap, VecDeque},
    fmt::{Display, Formatter, Result},
    mem,
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

    pub fn add_clause(&mut self, lits: Vec<Lit>) -> bool {
        if lits.is_empty() {
            return false;
        } else if lits.len() == 1 {
            return self.enqueue(lits[0], None);
        }

        let clause_id = self.clauses.len();
        for lit in &lits[..2] {
            if lit.is_positive() {
                self.pos_watches[lit.var()].push(clause_id);
            } else {
                self.neg_watches[lit.var()].push(clause_id);
            }
        }
        self.clauses.push(lits.to_vec());
        true
    }

    fn enqueue(&mut self, lit: Lit, reason: Option<usize>) -> bool {
        match self.value(lit.var()) {
            LBool::Undef => {
                self.assigns[lit.var()] = if lit.is_positive() { LBool::True } else { LBool::False };
                self.reason[lit.var()] = reason;
                self.prop_q.push_back(lit.var());
                if let Some(listeners) = self.listeners.get(&lit.var()) {
                    for listener in listeners {
                        listener(self, lit.var());
                    }
                }
                true
            }
            LBool::True => lit.is_positive(),
            LBool::False => !lit.is_positive(),
        }
    }

    pub fn assert(&mut self, lit: Lit) -> bool {
        self.enqueue(lit, None);
        while let Some(var) = self.prop_q.pop_front() {
            for clause in if self.value(var) == &LBool::True { mem::take(&mut self.neg_watches[var]) } else { mem::take(&mut self.pos_watches[var]) } {
                if !self.propagate(clause, Lit::new(var, self.value(var) == &LBool::True)) {
                    return false;
                }
            }
        }
        true
    }

    fn propagate(&mut self, clause_id: usize, lit: Lit) -> bool {
        // Ensure the first literal is not the one that was just assigned
        if self.clauses[clause_id][0].var() == lit.var() {
            self.clauses[clause_id].swap(0, 1);
        }
        // Check if clause is already satisfied
        if self.lit_value(&self.clauses[clause_id][0]) == LBool::True {
            // Re-add the clause to the watch list
            if lit.is_positive() {
                self.pos_watches[lit.var()].push(clause_id);
            } else {
                self.neg_watches[lit.var()].push(clause_id);
            }
            return true;
        }

        // Find the next unassigned literal
        for i in 2..self.clauses[clause_id].len() {
            if self.lit_value(&self.clauses[clause_id][i]) != LBool::False {
                // Move this literal to the second position
                self.clauses[clause_id].swap(1, i);
                // Update watch lists
                if self.clauses[clause_id][1].is_positive() {
                    self.pos_watches[self.clauses[clause_id][1].var()].push(clause_id);
                } else {
                    self.neg_watches[self.clauses[clause_id][1].var()].push(clause_id);
                }
                return true;
            }
        }

        // If we reach here, the clause is either unit or unsatisfied
        if lit.is_positive() {
            self.neg_watches[lit.var()].push(clause_id);
        } else {
            self.pos_watches[lit.var()].push(clause_id);
        }
        self.enqueue(self.clauses[clause_id][0], Some(clause_id))
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
