use std::{sync::Arc};

use graphviz_rust::{cmd::{CommandArg, Format}, exec_dot};

use crate::{ConcurrentSchedule, DependencyNode, OpType, VecOperation, RWSContext, ScAddr, TxId};

use super::concurrent_schedule::{LinkedList, SCSchedule};

pub enum NodeColor {
    LightBlue,
    LightGrey,
    
    // Background colors with hex codes
    BackgroundBlue,         
    BackgroundLavender,     
    BackgroundHoneydew,     
    BackgroundLightCyan,    
    BackgroundMintCream,    
    BackgroundAzure,        
    BackgroundIvory,        
    BackgroundSeashell,     
    BackgroundBeige,        
    BackgroundLemonChiffon, 
    BackgroundMistyRose,   
    BackgroundLavenderBlush,
    BackgroundOldLace,      
}

impl NodeColor {
    fn as_str(&self) -> &'static str {
        match self {
            NodeColor::LightBlue => "lightblue",
            NodeColor::LightGrey => "#F3F3F3",

            NodeColor::BackgroundBlue => "#9A86A4",
            NodeColor::BackgroundLavender => "#B1BCE6",
            NodeColor::BackgroundHoneydew => "#B7E5DD",
            NodeColor::BackgroundLightCyan => "#F1F0C0",

            NodeColor::BackgroundMintCream => "#F6A9A9",
            NodeColor::BackgroundAzure => "#FFBF86",
            NodeColor::BackgroundIvory => "#FFF47D",
            NodeColor::BackgroundSeashell => "#C2F784",

            NodeColor::BackgroundBeige => "#EDD2F3",
            NodeColor::BackgroundLemonChiffon => "#FFFCDC",
            NodeColor::BackgroundMistyRose => "#FFE4E1",
            NodeColor::BackgroundLavenderBlush => "#516BEB",
            NodeColor::BackgroundOldLace => "#8E806A",
        }
    }
}


pub struct DotSchedule<'a> {
    pub key_color: NodeColor,
    pub key_width: i32,

    node_colors: Vec<NodeColor>,
    rws: Option<&'a Arc<Vec<RWSContext>>>,
}

impl<'a> DotSchedule<'a> {

    pub fn new(key_color: NodeColor, key_width: i32) -> Self {
        use NodeColor::*;
        Self {
            key_color,
            key_width,
            node_colors: vec![
                BackgroundBlue, BackgroundLavender, BackgroundHoneydew, BackgroundLightCyan, BackgroundMintCream, 
                BackgroundAzure, BackgroundIvory, BackgroundSeashell, BackgroundBeige, BackgroundLemonChiffon,
                BackgroundMistyRose, BackgroundLavenderBlush, BackgroundOldLace
            ],
            rws: None,
        }
    }

    pub fn parse(&mut self, schedule: &ConcurrentSchedule,  rws: &'a Arc<Vec<RWSContext>>) -> String {
        self.rws = Some(rws);
        let mut file = String::new();
        file.push_str("digraph G {");
        file.push_str("\n    compound=true;");
        file.push_str("\n    rankdir=LR;");
        file.push_str("\n    node [shape=box];");

        file.push_str(&format!("{}", &self.generate_contracts(schedule)));
        
        file.push_str("\n}");

        file
    }

    fn generate_contracts(&self, schedule: &ConcurrentSchedule) -> String {
        let mut contracts = String::new();
        let mut contract_id = 0;

        for schedule in schedule {
            let contract_prefix = format!("c{}", contract_id);
            let contract_address = *schedule.key();

            let contract_schedule = schedule.value();
            contracts.push_str(&self.generate_contract(contract_schedule, contract_id, contract_address, &contract_prefix));
            
            contract_id += 1;
        };

        contracts
    }

    fn generate_contract(&self, schedule: &SCSchedule, contract_id: i32, contract_address: ScAddr, contract_prefix: &String) -> String {
        let mut contract = String::new();
        contract.push_str(&format!("\n    subgraph cluster_contract_{} {{", contract_id));
        contract.push_str(&format!("\n        label = \"{:?}\";", contract_address));
        contract.push_str(&format!("\n        rankdir=TB;"));
        contract.push_str(&format!("\n        style=\"filled\";"));
        contract.push_str(&format!("\n        fillcolor=\"{}\";", NodeColor::LightGrey.as_str()));
        contract.push_str(&format!("\n        color=black;"));

        contract.push_str(&self.generate_keys(schedule, contract_prefix));

        contract.push_str(&format!("\n    }}"));
        contract
    }

    fn generate_keys(&self, schedule: &SCSchedule, contract_prefix: &String) -> String {
        let mut keys = String::new();
        let mut key_id = 0;

        for key_schedule in schedule {
            let key_prefix = format!("_k{}", key_id);
            let key = key_schedule.key();
            let operations = key_schedule.value();

            keys.push_str(&self.generate_key(operations, key, &key_prefix, contract_prefix));

            key_id += 1;
        };

        keys
    }

    fn generate_key(&self, operations: &Arc<LinkedList<VecOperation>>, key_bytes: &Vec<u8>, key_prefix: &String, contract_prefix: &String) -> String {
        let contract_key_prefix = format!("{}{}", contract_prefix, key_prefix);

        let mut key = String::new();
        key.push_str(&format!("\n        subgraph cluster_{} {{", contract_key_prefix));
        key.push_str(&format!("\n            label = \"\";"));
        key.push_str(&format!("\n            rank=same;"));
        key.push_str(&format!("\n            style=\"filled\";"));
        key.push_str(&format!("\n            color=\"{}\";", NodeColor::LightGrey.as_str()));

        // key node config
        key.push_str(&format!("\n                {} [width={:?}, label=\"{:02X?}\", style=\"filled\", fillcolor=\"{}\"];", 
                                contract_key_prefix, self.key_width, &key_bytes[..8],                self.key_color.as_str()));

        key.push_str(&self.generate_operation_labels(operations, &contract_key_prefix));

        key.push_str(&format!("\n            edge [constraint=true]"));
        key.push_str(&self.generate_operations_sequence(operations, &contract_key_prefix));
        key.push_str(&format!("\n            edge [constraint=false]"));
        key.push_str(&self.generate_operation_dependencies(operations, &contract_key_prefix));

        key.push_str(&format!("\n        }}"));
        key
        // for schedule in contract_schedule {
        //     let key = schedule.key();
        //     let linked_list = schedule.value();
        //     let mut node = Arc::clone(&linked_list.head.read().unwrap());


  

        // };
    }

    fn generate_operation_labels(&self, operations: &Arc<LinkedList<VecOperation>>, contract_key_prefix: &String) -> String {
        self.apply_for_each_node(operations, contract_key_prefix, |node_id, node| -> String {
            let mut node_config = String::new();
            node_config.push_str(&format!("\n            {} ", node_id ));
            node_config.push_str(&self.generate_node_layout(node));
            node_config
        })
    }

    fn generate_operations_sequence(&self, operations: &Arc<LinkedList<VecOperation>>, contract_key_prefix: &String) -> String {
        let mut sequence = String::new();
        sequence.push_str(&format!("\n            {}", contract_key_prefix));
        let nodes = self.apply_for_each_node(operations, contract_key_prefix, |node_id, _node| -> String {
            let mut node_seq = String::new();
            node_seq.push_str(&format!(" -> {}", node_id ));
            node_seq
        });
        sequence.push_str(&nodes);
        sequence.push_str(" [dir=back, style=\"dotted\", arrowsize=0.2];");
        sequence
    }

    fn generate_operation_dependencies(&self, operations: &Arc<LinkedList<VecOperation>>, contract_key_prefix: &String) -> String {
        let dependencies = self.apply_for_each_node(operations, contract_key_prefix, |node_id, node| -> String {
            let mut idx = 0;
            // if node has a dependency
            if let Some(dependency) = node.dependency.as_ref() {

                let mut track_back_node = Arc::clone(&dependency); 

                // run through all nodes until reaching the head - to get the node idx to mark the dependency
                loop {
                    let node_lock = track_back_node.read().unwrap();                   
                    if let Some(prev_node) = node_lock.prev.clone() {
                        drop(node_lock);
        
                        track_back_node = prev_node;
                        idx += 1;
                    }
                    else { break }
                }

                let dependency_node_id = format!("{}_Op{}", contract_key_prefix, idx);
                return format!("\n            {} -> {} [color=red, penwidth=3.0];", node_id, dependency_node_id)
            }

            "".to_owned()
        });
        dependencies
    }


    fn apply_for_each_node<F>(&self, operations: &Arc<LinkedList<VecOperation>>, contract_key_prefix: &String, string_builder: F) -> String 
    where
        F: Fn(&String, &DependencyNode<VecOperation>) -> String
    {
        let mut content = String::new();
        let mut op_idx = 0;
        let mut node = Arc::clone(&operations.head.read().unwrap());

        loop {
            let node_id = format!("{}_Op{}", contract_key_prefix, op_idx);
            let node_lock = node.read().unwrap();
            
            let string = string_builder(&node_id, &node_lock);
            content.push_str(&format!("{}", string));
            
            if let Some(next_node) = node_lock.next.clone() {
                drop(node_lock);

                node = next_node;
                op_idx += 1;
            }
            else {
                break;
            }
        }

        content
    }


    fn generate_node_layout(&self, node: &DependencyNode<VecOperation>) -> String {
        let mut completeness = None;
        let mut storage_dependency = None;

        for rws in &**self.rws.unwrap() {
            if node.data.is_from_tx(rws.tx_block_id) {
                completeness = Some(rws.rws.profile_status);
                storage_dependency = Some(rws.rws.storage_dependency);
                break;
            }
        }

        let color = node.data.tx_block_id % self.node_colors.len();
        format!(r#"[label=<
                <table border="0" cellborder="1" cellspacing="0">
                <tr><td><b>Transaction        </b></td><td>{}  </td></tr>
                <tr><td><b>Operation          </b></td><td>{:?}</td></tr>
                <tr><td><b>Commutativity      </b></td><td>{:?}</td></tr>
                <tr><td><b>Value              </b></td><td>{:?}</td></tr>
                <tr><td><b>Profile            </b></td><td>{:?}</td></tr>
                <tr><td><b>Storage Dependency </b></td><td>{:?}</td></tr>
                </table>
                >, style="filled", shape=plaintext, fontname="Arial", fontsize=12, fontcolor=black, fillcolor="{}", color=black, penwidth=2];        
        "#,
            node.data.tx_block_id, 
            node.data.operation_type,
            node.data.commutativity, 
            node.data.value.get_value(),
            completeness.unwrap(),
            storage_dependency.unwrap(),
            self.node_colors[color].as_str(),
        )
    }

    pub fn save_as_png(&self, dot: String, name_suffix: String) -> std::io::Result<()> {
        // Convert the DOT string to a graph
        let graph_name = format!("graph_{}.png", name_suffix);
        // Generate the PNG
        exec_dot(
            dot,
            vec![
                CommandArg::Format(Format::Png),
                CommandArg::Output(graph_name.clone()),
            ],
        )
        .unwrap();

        // The PNG has been saved to "debug_graph.png"
        println!("Debug graph generated: {}", graph_name);

        Ok(())
    }
}