mod lit;

use std::collections::{HashMap, VecDeque};

use crate::lit::LBool;
pub use lit::Lit;
type Callback = Box<dyn Fn(&Engine, usize)>;

#[derive(Default)]
struct Var {
    value: LBool,                   // current value
    current_level_vars: Vec<usize>, // variables assigned at the current decision level
    decision_var: Option<usize>,    // decision variable that led to this assignment
    reason: Option<usize>,          // clause that implied the value
    pos_clauses: Vec<usize>,        // clauses where the variable appears positively
    neg_clauses: Vec<usize>,        // clauses where the variable appears negatively
}

#[derive(Default)]
pub struct Engine {
    vars: Vec<Var>,
    clauses: Vec<Vec<Lit>>,
    prop_q: VecDeque<usize>,
    listeners: HashMap<usize, Vec<Callback>>,
}

impl Engine {
    pub fn new() -> Self {
        Engine::default()
    }
}
