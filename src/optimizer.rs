//! This file isn't actually used right now, but it has some basic work towards
//! building a DAG.

use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
};

use crate::ir::{CompareAction, Instruction, Label};

#[derive(Debug)]
pub struct CodeGraph {
    nodes: HashMap<Option<usize>, Node>,
    cycles: HashMap<usize, Vec<usize>>,
    references: HashMap<usize, Vec<Option<usize>>>,
}

impl Display for CodeGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut node_ids = self.nodes.keys().copied().collect::<Vec<_>>();
        node_ids.sort_unstable();

        for node_id in node_ids {
            let node = self.nodes.get(&node_id).expect("keys came from collection");
            if let Some(node_id) = node_id {
                if let Some(label) = node.label {
                    writeln!(f, "Node {node_id} ({label}):")?;
                } else {
                    writeln!(f, "Node {node_id}:")?;
                }
            } else {
                f.write_str("Entry Node:\n")?;
            }
            for i in &node.instructions {
                writeln!(f, "    {i}")?;
            }

            writeln!(f, "  Possible Next Locations: {}", node.possible_branches)?;
        }

        Ok(())
    }
}

impl CodeGraph {
    pub fn new(instructions: &[Instruction]) -> Self {
        let mut nodes = HashMap::new();
        // Find all labels so that we can
        let mut labeled_nodes = Vec::new();
        for i in instructions {
            if let Instruction::Label(label) = i {
                let node_id = nodes.len();
                nodes.insert(
                    Some(node_id),
                    Node {
                        label: Some(*label),
                        ..Node::default()
                    },
                );
                if labeled_nodes.len() <= label.0 {
                    labeled_nodes.resize(label.0 + 1, None);
                }

                labeled_nodes[label.0] = Some(node_id);
            }
        }

        // Iterate over the instructions grouping them into chunks where the
        // only branching instruction in a chunk might be the last one.
        let mut next_node_id = nodes.len();
        let mut current_node = nodes.entry(None).or_default();
        for i in instructions {
            if let Instruction::Label(label) = i {
                // Labels are natural splits since a jump should target it. The
                // current node only has one possible target: the next node.
                let label_node = labeled_nodes[label.0].unwrap();
                current_node.possible_branches = BranchTargets::Node(label_node);
                current_node = nodes.entry(Some(label_node)).or_default();
            } else {
                current_node.instructions.push(i.clone());
                if let Some(branch_targets) = PossibleBranches::identify(i) {
                    match branch_targets {
                        PossibleBranches::Jump(label) => {
                            current_node.possible_branches =
                                BranchTargets::Node(labeled_nodes[label.0].unwrap());
                        }
                        PossibleBranches::NextOrJump(label) => {
                            current_node.possible_branches =
                                BranchTargets::Split(next_node_id, labeled_nodes[label.0].unwrap());
                        }
                        PossibleBranches::Next => {
                            current_node.possible_branches = BranchTargets::Node(next_node_id);
                        }
                        PossibleBranches::Return => {
                            current_node.possible_branches = BranchTargets::Return;
                        }
                    }

                    current_node = nodes.entry(Some(next_node_id)).or_default();
                    next_node_id += 1;
                }
            }
        }

        let mut graph = Self {
            nodes,
            cycles: HashMap::new(),
            references: HashMap::new(),
        };

        graph.detect_cycles(None, &mut Vec::new());

        graph
    }

    /// Returns the graph divided into acyclic regions.
    pub fn dags(&self) -> Dag {
        // Now that we have a list of cycles, we can
        if self.cycles.is_empty() {
            Dag {
                start_node: None,
                member_nodes: self.references.keys().copied().collect(),
            }
        } else {
            todo!(
                "need to condense the graph into a dag of cyclic regions that are treated as nodes"
            )
        }
    }

    fn detect_cycles(&mut self, node_id: Option<usize>, current_path: &mut Vec<usize>) {
        if let Some(node_id) = node_id {
            current_path.push(node_id);
        }

        let node = self.nodes.get(&node_id).expect("node id not found");
        for next in &node.possible_branches {
            self.references.entry(next).or_default().push(node_id);
            if current_path.contains(&next) {
                let cycles = self.cycles.entry(next).or_insert_with(Vec::new);
                cycles.push(node_id.expect("entry node cannot cycle"));
            } else {
                self.detect_cycles(Some(next), current_path);
            }
        }

        // Remove our node id from the path before returning
        current_path.pop();
    }
}

enum PossibleBranches {
    Jump(Label),
    NextOrJump(Label),
    Next,
    Return,
}

impl PossibleBranches {
    fn identify(instruction: &Instruction) -> Option<Self> {
        match instruction {
            Instruction::If { false_jump_to, .. } => Some(Self::NextOrJump(*false_jump_to)),
            Instruction::JumpTo(label) => Some(Self::Jump(*label)),
            Instruction::Compare {
                action: CompareAction::JumpIfFalse(label),
                ..
            } => Some(Self::NextOrJump(*label)),
            Instruction::Return(_) => Some(Self::Return),
            _ => None,
        }
    }
}

#[derive(Default, Debug)]
pub struct Node {
    label: Option<Label>,
    instructions: Vec<Instruction>,
    possible_branches: BranchTargets,
}

impl Node {
    pub fn optimize(&mut self) {
        self.remove_unnecessary_loads();
    }

    fn remove_unnecessary_loads(&mut self) {
        let mut instruction_index = 0;
        while instruction_index < self.instructions.len() {
            if let Instruction::Load { value, variable } = &self.instructions[instruction_index] {
                // Determine
            }
        }
    }
}

#[derive(Debug, Clone)]
enum BranchTargets {
    Split(usize, usize),
    Node(usize),
    Return,
}

impl Iterator for BranchTargets {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            BranchTargets::Split(a, b) => {
                let a = *a;
                *self = BranchTargets::Node(*b);
                Some(a)
            }
            BranchTargets::Node(a) => {
                let a = *a;
                *self = BranchTargets::Return;
                Some(a)
            }
            BranchTargets::Return => None,
        }
    }
}

impl<'a> IntoIterator for &'a BranchTargets {
    type Item = usize;

    type IntoIter = BranchTargets;

    fn into_iter(self) -> Self::IntoIter {
        self.clone()
    }
}

impl Default for BranchTargets {
    fn default() -> Self {
        Self::Return
    }
}

impl Display for BranchTargets {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BranchTargets::Split(a, b) => write!(f, "{a}, {b}"),
            BranchTargets::Node(node) => Display::fmt(node, f),
            BranchTargets::Return => f.write_str("return"),
        }
    }
}

#[derive(Debug)]
pub struct Dag {
    start_node: Option<usize>,
    member_nodes: HashSet<usize>,
}

impl Dag {
    pub fn optimize(&self, graph: &mut CodeGraph) {
        let mut nodes_to_scan = vec![self.start_node];

        while let Some(node_id) = nodes_to_scan.pop() {
            // if node_id.is_none() || self.member_nodes.contains(&node_id.expect("just checked")) {

            let node = graph.nodes.get_mut(&node_id).expect("node id not found");
            node.optimize();
            // }
        }
    }
}
