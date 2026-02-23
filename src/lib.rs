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
    propagated_vars: Vec<Vec<usize>>,         // Variables that have been propagated by decision variables
    decision_vars: Vec<Option<usize>>,        // Decision variables that caused the propagation of each variable
    decision_var: usize,                      // Current decision variable index
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
        self.propagated_vars.push(Vec::new());
        self.decision_vars.push(None);
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

    /// Returns the decision variable that caused the propagation of the given variable, if any.
    pub fn decision_var(&self, var: usize) -> Option<usize> {
        self.decision_vars[var]
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
                if lit.var() != self.decision_var {
                    self.propagated_vars[self.decision_var].push(lit.var());
                    self.decision_vars[lit.var()] = Some(self.decision_var);
                }
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
        assert!(self.value(lit.var()) == &LBool::Undef, "Variable b{} is already assigned", lit.var());
        self.decision_var = lit.var();
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

    pub fn retract(&mut self, var: usize) {
        assert!(self.value(var) != &LBool::Undef, "Variable b{} is not assigned", var);
        if let Some(decision_var) = self.decision_vars[var] {
            for propagated_var in mem::take(&mut self.propagated_vars[decision_var]) {
                self.undo(propagated_var);
            }
        } else {
            for propagated_var in mem::take(&mut self.propagated_vars[var]) {
                self.undo(propagated_var);
            }
            self.undo(var);
        }
    }

    fn undo(&mut self, var: usize) {
        assert!(self.propagated_vars[var].is_empty(), "Variable b{} has propagated variables that must be retracted first", var);
        self.assigns[var] = LBool::Undef;
        self.reason[var] = None;
        self.decision_vars[var] = None;
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lit::{neg, pos};

    #[test]
    fn test_basic_assignment_and_value() {
        let mut engine = Engine::new();
        let a = engine.add_var();

        assert_eq!(*engine.value(a), LBool::Undef);

        engine.assert(pos(a));
        assert_eq!(*engine.value(a), LBool::True);
        assert_eq!(engine.lit_value(&pos(a)), LBool::True);
        assert_eq!(engine.lit_value(&neg(a)), LBool::False);
    }

    #[test]
    fn test_unit_propagation_simple() {
        let mut engine = Engine::new();
        let a = engine.add_var();
        let b = engine.add_var();

        // Clause: (¬a ∨ b)  => If a is true, b must be true.
        engine.add_clause(vec![neg(a), pos(b)]);

        engine.assert(pos(a));

        // b should be propagated to True
        assert_eq!(*engine.value(b), LBool::True, "b should be propagated by unit clause");
        assert_eq!(engine.decision_var(b), Some(a), "a should be the decision variable for b");
    }

    #[test]
    fn test_chained_propagation() {
        let mut engine = Engine::new();
        let a = engine.add_var();
        let b = engine.add_var();
        let c = engine.add_var();

        // (¬a ∨ b) and (¬b ∨ c)
        // a -> b -> c
        engine.add_clause(vec![neg(a), pos(b)]);
        engine.add_clause(vec![neg(b), pos(c)]);

        engine.assert(pos(a));

        assert_eq!(*engine.value(c), LBool::True, "c should propagate via b");
    }

    #[test]
    fn test_two_watched_literals_movement() {
        let mut engine = Engine::new();
        let a = engine.add_var();
        let b = engine.add_var();
        let c = engine.add_var();

        // Clause: (a ∨ b ∨ c)
        // Initially watching a and b.
        engine.add_clause(vec![pos(a), pos(b), pos(c)]);

        // Assign a = False.
        // 2WL should move watch from 'a' to 'c' because 'b' is still Undef.
        engine.assert(neg(a));
        assert_eq!(*engine.value(b), LBool::Undef, "b should still be undef");
        assert_eq!(*engine.value(c), LBool::Undef, "c should still be undef");

        // Now assign b = False.
        // This should trigger propagation on c.
        engine.assert(neg(b));
        assert_eq!(*engine.value(c), LBool::True, "c must be true now");
    }

    #[test]
    fn test_retraction_logic() {
        let mut engine = Engine::new();
        let a = engine.add_var();
        let b = engine.add_var();

        engine.add_clause(vec![neg(a), pos(b)]);

        engine.assert(pos(a));
        assert_eq!(*engine.value(b), LBool::True);

        // Retract a
        engine.retract(a);

        assert_eq!(*engine.value(a), LBool::Undef, "a should be undone");
        assert_eq!(*engine.value(b), LBool::Undef, "b should be undone automatically");
    }

    #[test]
    fn test_listeners() {
        use std::sync::{Arc, Mutex};

        let mut engine = Engine::new();
        let a = engine.add_var();
        let b = engine.add_var();

        let triggered = Arc::new(Mutex::new(false));
        let triggered_clone = Arc::clone(&triggered);

        // Add listener to b
        engine.add_listener(b, move |_, _| {
            let mut val = triggered_clone.lock().unwrap();
            *val = true;
        });

        // (¬a ∨ b)
        engine.add_clause(vec![neg(a), pos(b)]);

        // Assert a, which propagates b, which should fire the listener
        engine.assert(pos(a));

        assert!(*triggered.lock().unwrap(), "Listener on b should have been triggered");
    }

    #[test]
    #[should_panic(expected = "already assigned")]
    fn test_double_assertion_panic() {
        let mut engine = Engine::new();
        let a = engine.add_var();
        engine.assert(pos(a));
        engine.assert(neg(a)); // Should panic
    }
}
