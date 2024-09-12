use crate::symb_exec::{ProfileEvaluator, ProfileGenerator, TxRWS};
use crate::SCProfile;

pub struct PerfectRWSEngine {
    rws_idx: u64,
}

impl ProfileGenerator for PerfectRWSEngine {
    // wont use the code for anything. Th eprofile swill serve no use
    fn generate_profile(&self, contract: &[u8]) -> SCProfile {
        SCProfile::default()
    }
}

impl ProfileEvaluator for PerfectRWSEngine {
    fn get_rws_instantiate<'a>(&self, sc_profile: &SCProfile, deps: &'a crate::DepsMut<'a>, custom: &[u8]) -> TxRWS {
        todo!()
    }

    fn get_rws_execute<'a>    (&self, sc_profile: &SCProfile, deps: &'a crate::DepsMut<'a>, custom: &[u8]) -> TxRWS {
        todo!()
    }

    fn get_rws_query<'a>      (&self, sc_profile: &SCProfile, deps: &'a crate::DepsMut<'a>, custom: &[u8]) -> TxRWS {
        todo!()
    }
}