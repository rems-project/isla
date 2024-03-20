use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

#[derive(Serialize, Deserialize, Debug, Clone, Copy, PartialEq, Eq)]
pub enum GraphMode {
    Disabled,
    ASCII,
    Dot,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct GraphOpts {
    pub mode: GraphMode,
    pub show_regs: HashSet<String>,
    pub flatten: bool,
    pub debug: bool,
    pub show_all_reads: bool,
    pub shows: Option<Vec<String>>,
    pub padding: Option<HashMap<String, f64>>,
    pub force_show_events: Option<Vec<String>>,
    pub force_hide_events: Option<Vec<String>>,
    pub squash_translation_labels: bool,
    pub control_delimit: bool,
    pub human_readable_values: bool,
}

impl GraphOpts {
    pub const DEFAULT_SHOW_REGS: &'static [&'static str] = &[
        "R0", "R1", "R2", "R3", "R4", "R5", "R6", "R7", "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15", "R16",
        "R18", "R18", "R19", "R20", "R21", "R22", "R23", "R24", "R25", "R26", "R27", "R28", "R29", "R30", "R31", "SP",
        "SP_EL0", "SP_EL1", "SP_EL2", "SP_EL3", "VBAR_EL1", "VBAR_EL2",
    ];

    pub const ARMV8_ADDR_TRANS_SHOW_REGS: &'static [&'static str] =
        &["TTBR0_EL1", "TTBR1_EL1", "TTBR0_EL2", "VTTBR_EL2"];

    /// by default we transitively reduce some relations to make them smaller
    /// can explicitly do this by postfixing a relation with -
    /// can also do the opposite by postfixing a relation with + to get the transitive closure instead.
    pub const DEFAULT_REL_TRANSITIVE_REDUCE: &'static [&'static str] =
        &["po", "iio", "fpo", "instruction-order", "co", "wco", "ctrl"];

    /// by default we do not show relations where a higher-priority one overrides it
    /// i.e. if e1 R e2 and e1 R' e2 and R' is higher priority then do not draw e1 R e2 in the graph.
    /// the below is a list of (R', R) where R' is the higher-priority one
    pub const DEFAULT_REL_PRIORITY: &'static [(&'static str, &'static str)] = &[
        // dependencies are subsets of po so don't render po between them separately
        ("addr", "po"),
        ("ctrl", "po"),
        ("data", "po"),
        // co is a subset of wco
        ("co", "wco"),
    ];
}
