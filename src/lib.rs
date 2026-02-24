//! # SAT Solver Engine
//!
//! This module provides a core CDCL (Conflict-Driven Clause Learning) engine
//! utilizing the Two-Watched Literal (2WL) scheme for efficient unit propagation.
//!
//! ## Core Logic
//! The engine works by:
//! 1. **Assignment**: Values are assigned to variables via `assert`.
//! 2. **Propagation**: The engine uses watch lists to find unit clauses.
//! 3. **Conflict Analysis**: If a contradiction is found, the engine performs
//!    1-UIP (Unique Implication Point) analysis to learn a new clause.
//!
//! ## Example
//! ```rust
//! # use consensus::{Engine, pos, neg};
//! let mut engine = Engine::new();
//! let a = engine.add_var();
//! let b = engine.add_var();
//! engine.add_clause(vec![neg(a), pos(b)]); // (¬a ∨ b)
//! engine.assert(pos(a));                   // Forces b to be True
//! ```
use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet, VecDeque},
    fmt::{Display, Formatter, Result},
    mem,
    ops::Not,
};

type Callback = Box<dyn Fn(&Engine, usize)>;

#[derive(Clone, Debug, PartialEq, Eq, Default)]
#[repr(u8)]
pub enum LBool {
    True,
    False,
    #[default]
    Undef,
}

impl Display for LBool {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let s = match self {
            LBool::True => "True",
            LBool::False => "False",
            LBool::Undef => "Undef",
        };
        write!(f, "{}", s)
    }
}

/// A literal is represented as a variable index and a sign (true for positive, false for negative).
///
/// # Examples
/// ```
/// # use consensus::{Lit, pos, neg};
/// let a = pos(0); // Represents the literal b0
/// let not_a = neg(0); // Represents the literal ¬b0
///
/// assert_eq!(a.var(), 0);
/// assert!(a.is_positive());
/// assert_eq!(not_a.var(), 0);
/// assert!(!not_a.is_positive());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Lit {
    x: usize,
    sign: bool,
}

impl Lit {
    pub fn new(x: usize, sign: bool) -> Self {
        Lit { x, sign }
    }

    pub fn pos(x: usize) -> Self {
        Lit { x, sign: true }
    }

    pub fn neg(x: usize) -> Self {
        Lit { x, sign: false }
    }

    pub fn var(&self) -> usize {
        self.x
    }

    pub fn is_positive(&self) -> bool {
        self.sign
    }
}

pub fn pos(x: usize) -> Lit {
    Lit::pos(x)
}

pub fn neg(x: usize) -> Lit {
    Lit::neg(x)
}

impl Default for Lit {
    fn default() -> Self {
        Lit { x: usize::MAX, sign: false }
    }
}

impl Display for Lit {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self.sign {
            true => write!(f, "b{}", self.x),
            false => write!(f, "¬b{}", self.x),
        }
    }
}

impl Not for Lit {
    type Output = Lit;

    fn not(self) -> Lit {
        Lit { x: self.x, sign: !self.sign }
    }
}

impl Not for &Lit {
    type Output = Lit;

    fn not(self) -> Lit {
        Lit { x: self.x, sign: !self.sign }
    }
}

impl PartialOrd for Lit {
    fn partial_cmp(&self, other: &Lit) -> Option<Ordering> {
        match self.x.partial_cmp(&other.x) {
            Some(Ordering::Equal) => self.sign.partial_cmp(&other.sign),
            ord => ord,
        }
    }
}

pub struct Clause {
    pub lits: Vec<Lit>,
}

impl Display for Clause {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let lits: Vec<String> = self.lits.iter().map(|l| l.to_string()).collect();
        write!(f, "{}", lits.join(" ∨ "))
    }
}

/// A CDCL-based SAT solver engine.
///
/// The `Engine` manages variable assignments, watch lists for unit propagation,
/// and performs conflict analysis to learn new clauses.
///
/// # Examples
/// ```
/// # use consensus::{Engine, pos, neg, LBool};
/// let mut engine = Engine::new();
/// let a = engine.add_var();
/// let b = engine.add_var();
/// engine.add_clause(vec![neg(a), pos(b)]); // (¬a ∨ b)
/// engine.assert(pos(a));                   // Forces b to be True
/// assert_eq!(*engine.value(b), LBool::True, "b should be propagated by unit clause");
/// ```
pub struct Engine {
    assigns: Vec<LBool>,                      // Current assignments of variables
    reason: Vec<Option<usize>>,               // Reason for each variable's assignment (index of the clause that caused the assignment)
    propagated_vars: Vec<usize>,              // Variables that have been propagated by decision variables
    decision_vars: Vec<Option<usize>>,        // Decision variables that caused the propagation of each variable
    decision_var: usize,                      // Current decision variable index
    pos_watches: Vec<Vec<usize>>,             // Clauses watching the positive literal of each variable
    neg_watches: Vec<Vec<usize>>,             // Clauses watching the negative literal of each variable
    clauses: Vec<Clause>,                     // List of clauses in the engine
    prop_q: VecDeque<usize>,                  // Queue of variables to propagate
    learnt: Vec<Lit>,                         // Temporary storage for learnt clauses during conflict analysis
    listeners: HashMap<usize, Vec<Callback>>, // Listeners for variable assignments
}

impl Default for Engine {
    fn default() -> Self {
        Self::new()
    }
}

impl Engine {
    pub fn new() -> Self {
        Engine {
            assigns: Vec::new(),
            reason: Vec::new(),
            propagated_vars: Vec::new(),
            decision_vars: Vec::new(),
            decision_var: usize::MAX, // No decision variable initially
            pos_watches: Vec::new(),
            neg_watches: Vec::new(),
            clauses: Vec::new(),
            prop_q: VecDeque::new(),
            learnt: Vec::new(),
            listeners: HashMap::new(),
        }
    }

    pub fn add_var(&mut self) -> usize {
        let var_id = self.assigns.len();
        self.assigns.push(LBool::Undef);
        self.reason.push(None);
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
        self.clauses.push(Clause { lits });
        true
    }

    pub fn assert(&mut self, lit: Lit) -> bool {
        assert!(self.value(lit.var()) == &LBool::Undef, "Variable b{} is already assigned", lit.var());
        self.decision_var = lit.var();
        self.propagated_vars.clear();
        self.enqueue(lit, None);
        while let Some(var) = self.prop_q.pop_front() {
            let watches = if self.value(var) == &LBool::True { mem::take(&mut self.neg_watches[var]) } else { mem::take(&mut self.pos_watches[var]) };
            for i in 0..watches.len() {
                if !self.propagate(watches[i], Lit::new(var, self.value(var) == &LBool::True)) {
                    for j in i..watches.len() {
                        if self.value(var) == &LBool::True {
                            self.neg_watches[var].push(watches[j]);
                        } else {
                            self.pos_watches[var].push(watches[j]);
                        }
                    }
                    self.prop_q.clear();
                    self.analyze_conflict(watches[i]);
                    return false;
                }
            }
        }
        true
    }

    pub fn get_conflict_explanation(&mut self) -> Option<Clause> {
        if self.learnt.is_empty() { None } else { Some(Clause { lits: mem::take(&mut self.learnt) }) }
    }

    fn enqueue(&mut self, lit: Lit, reason: Option<usize>) -> bool {
        match self.value(lit.var()) {
            LBool::Undef => {
                self.assigns[lit.var()] = if lit.is_positive() { LBool::True } else { LBool::False };
                self.reason[lit.var()] = reason;
                self.propagated_vars.push(lit.var());
                if lit.var() != self.decision_var {
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

    fn analyze_conflict(&mut self, mut clause: usize) {
        let mut seen = HashSet::new();
        let mut counter: usize = 0;
        let mut p: Option<(Lit, Option<usize>)> = None;
        self.learnt.clear();
        self.learnt.push(Lit::default()); // Placeholder for the asserting literal

        loop {
            // 1. Process the current clause (either the conflict or a reason)
            for lit in &self.clauses[clause].lits {
                let v = lit.var();

                // Skip the variable we are currently resolving away
                if Some(v) == p.map(|l| l.0.var()) {
                    continue;
                }

                if !seen.contains(&v) {
                    seen.insert(v);
                    if self.decision_vars[v] == Some(self.decision_var) {
                        counter += 1;
                    } else {
                        // This literal comes from a previous decision level
                        self.learnt.push(lit.clone());
                    }
                }
            }

            // 2. Find the next variable from the trail assigned at this level
            p = loop {
                let v = self.propagated_vars.pop().expect("There should be a variable to resolve away");
                if seen.contains(&v) {
                    let sign = self.value(v) == &LBool::True;
                    let reason = self.reason[v];
                    self.undo(v);
                    break Some((Lit::new(v, sign), reason));
                }
                self.undo(v);
            };

            counter -= 1;

            // 3. Check for 1-UIP (First Unique Implication Point)
            if counter == 0 {
                self.learnt[0] = !p.expect("There should be a literal to assert").0;
                break;
            }

            // 4. Update clause to the reason of the variable we just resolved away
            clause = p.expect("There should be a reason clause for this variable").1.expect("There should be a reason clause for this variable");
        }

        // 5. Final cleanup - undo all assignments made at this level
        while !self.propagated_vars.is_empty() {
            let var = self.propagated_vars.pop().unwrap();
            self.undo(var);
        }
        self.undo(self.decision_var);
    }

    pub fn undo(&mut self, var: usize) {
        self.assigns[var] = LBool::Undef;
        self.reason[var] = None;
        self.decision_vars[var] = None;
    }

    fn propagate(&mut self, clause_id: usize, lit: Lit) -> bool {
        // Ensure the first literal is not the one that was just assigned
        if self.clauses[clause_id].lits[0].var() == lit.var() {
            self.clauses[clause_id].lits.swap(0, 1);
        }
        // Check if clause is already satisfied
        if self.lit_value(&self.clauses[clause_id].lits[0]) == LBool::True {
            // Re-add the clause to the watch list
            if lit.is_positive() {
                self.pos_watches[lit.var()].push(clause_id);
            } else {
                self.neg_watches[lit.var()].push(clause_id);
            }
            return true;
        }

        // Find the next unassigned literal
        for i in 2..self.clauses[clause_id].lits.len() {
            if self.lit_value(&self.clauses[clause_id].lits[i]) != LBool::False {
                // Move this literal to the second position
                self.clauses[clause_id].lits.swap(1, i);
                // Update watch lists
                if self.clauses[clause_id].lits[1].is_positive() {
                    self.pos_watches[self.clauses[clause_id].lits[1].var()].push(clause_id);
                } else {
                    self.neg_watches[self.clauses[clause_id].lits[1].var()].push(clause_id);
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
        self.enqueue(self.clauses[clause_id].lits[0], Some(clause_id))
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
            writeln!(f, "{}", clause)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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

    #[test]
    fn test_diamond_propagation() {
        let mut engine = Engine::new();
        let x1 = engine.add_var();
        let x2 = engine.add_var();
        let x3 = engine.add_var();
        let x4 = engine.add_var();

        // x1 -> x2  (¬x1 ∨ x2)
        engine.add_clause(vec![neg(x1), pos(x2)]);
        // x1 -> x3  (¬x1 ∨ x3)
        engine.add_clause(vec![neg(x1), pos(x3)]);
        // (x2 ∧ x3) -> x4 (¬x2 ∨ ¬x3 ∨ x4)
        engine.add_clause(vec![neg(x2), neg(x3), pos(x4)]);

        engine.assert(pos(x1));

        assert_eq!(*engine.value(x4), LBool::True, "x4 should be forced via x2 and x3");
    }

    #[test]
    fn test_complex_conflict_1uip() {
        let mut engine = Engine::new();
        let vars: Vec<usize> = (0..10).map(|_| engine.add_var()).collect();

        // Setup a chain: x1 -> x2 -> x3 -> x4
        engine.add_clause(vec![neg(vars[1]), pos(vars[2])]);
        engine.add_clause(vec![neg(vars[2]), pos(vars[3])]);
        engine.add_clause(vec![neg(vars[3]), pos(vars[4])]);

        // Create a conflict path:
        // (x4 ∧ x5) -> Conflict
        // x5 is another decision or forced var
        engine.add_clause(vec![neg(vars[4]), neg(vars[5])]);

        // Another path to the same conflict
        // (x3 ∧ x6) -> x5
        engine.add_clause(vec![neg(vars[3]), neg(vars[6]), pos(vars[5])]);

        // Assert "side" variables that set the stage
        engine.assert(pos(vars[6]));

        // Now trigger the chain
        // This should cause: x1 -> x2 -> x3 -> x4 -> conflict with x5
        let success = engine.assert(pos(vars[1]));

        assert!(!success, "Should detect a conflict");

        let explanation = engine.get_conflict_explanation().unwrap();
        // The explanation should ideally contain the 1-UIP literal
        // and the "reason" variables from lower levels.
        assert!(!explanation.lits.is_empty());
        println!("Conflict explanation: {}", explanation);
    }

    #[test]
    fn test_conflict_analysis() {
        let mut engine = Engine::new();
        let x1 = engine.add_var();
        let x2 = engine.add_var();
        let x3 = engine.add_var();
        let x4 = engine.add_var();
        let x5 = engine.add_var();
        let x6 = engine.add_var();
        let x7 = engine.add_var();
        let x8 = engine.add_var();
        let x9 = engine.add_var();

        // (x1 ∨ x2)
        engine.add_clause(vec![pos(x1), pos(x2)]);
        // (x1 ∨ x3 ∨ x7)
        engine.add_clause(vec![pos(x1), pos(x3), pos(x7)]);
        // (¬x2 ∨ ¬x3 ∨ x4)
        engine.add_clause(vec![neg(x2), neg(x3), pos(x4)]);
        // (¬x4 ∨ x5 ∨ x8)
        engine.add_clause(vec![neg(x4), pos(x5), pos(x8)]);
        // (¬x4 ∨ x6 ∨ x9)
        engine.add_clause(vec![neg(x4), pos(x6), pos(x9)]);
        // (¬x5 ∨ ¬x6)
        engine.add_clause(vec![neg(x5), neg(x6)]);

        // Assert ¬x7
        engine.assert(neg(x7));
        // Assert ¬x8
        engine.assert(neg(x8));
        // Assert ¬x9
        engine.assert(neg(x9));

        // Assert ¬x1, which should trigger conflict analysis
        engine.assert(neg(x1));

        let explanation = engine.get_conflict_explanation().expect("There should be a conflict explanation");
        let expected_explanation = vec![neg(x4), pos(x9), pos(x8)];
        assert_eq!(explanation.lits, expected_explanation, "Conflict explanation should match expected");
    }
}
