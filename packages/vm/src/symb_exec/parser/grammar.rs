#[allow(unused_imports)]
use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "symb_exec/parser/symb_exec.pest"]
struct SEParser;

#[cfg(test)]
pub mod tests {
    use pest::iterators::Pair;

    use super::*;

    /// Parse the input string as the specified Rule.
    /// Apply further assertions from the closure that is passed as input
    /// If the input string cannot be parsed (due to grammar errors), it panics.
    fn test_parser_f<F>(input: &str, base_rule: Rule, assert_further_rules: F)
    where
        F: FnOnce(Pair<Rule>)
    {
        match SEParser::parse(base_rule, input) {
            Ok(mut pairs) => {
                let pair: Pair<Rule> = pairs.next().unwrap();
                println!("Pair: {:?}", pair);
                assert_eq!(input, pair.as_str());
                assert_eq!(base_rule, pair.as_rule());
                
                assert_further_rules(pair.clone());
            },
            Err(e) => panic!("{:?}", e)
        }
    }

    /// Tests the generated pairs
    /// use when we want to test only the upper level rule
    fn test_parser(input: &str, base_rule: Rule){
        test_parser_f(input, base_rule, |_| {});
    }

    fn assert_error(input: &str, rule: Rule) {
        match SEParser::parse(rule, input) {
            Ok(_) => assert!(false),
            Err(_ ) => assert!(true),
        }
    }

    #[test]
    fn base64() {
        let hexa = "AARiYW5rQURNSU4=";
        let pair: Pair<Rule> = SEParser::parse(Rule::base64, hexa)
            .unwrap().next().unwrap();
        assert_eq!(hexa, pair.as_str());
    }

    #[test]
    fn rust_identifier() {
        let variable = "_variabl12_oj";
        let pair: Pair<Rule> = SEParser::parse(Rule::rust_identifier, variable)
            .unwrap().next().unwrap();
        assert_eq!(variable, pair.as_str());

        let variable = "v1";
        let pair: Pair<Rule> = SEParser::parse(Rule::rust_identifier, variable)
            .unwrap().next().unwrap();
        assert_eq!(variable, pair.as_str());

        assert_error("1vwe", Rule::rust_identifier); // not valid
    }

    #[test]
    fn attr_accessor() {
        // TEST 1
        let attr_access = "_variabl12_oj.hey";
        let variable = "_variabl12_oj";
        let field1 = "hey";

        match SEParser::parse(Rule::attr_accessor, attr_access) {
            Ok(mut pairs) => {
                let pair: Pair<Rule> = pairs.next().unwrap();
                assert_eq!(attr_access, pair.as_str());
                assert_eq!(Rule::attr_accessor, pair.as_rule());

                let var_name = pair.clone().into_inner().next().unwrap();
                assert_eq!(variable, var_name.as_str());
                assert_eq!(Rule::rust_identifier, var_name.as_rule());

                let field = pair.into_inner().nth(1).unwrap();
                assert_eq!(field1, field.as_str());
                assert_eq!(Rule::rust_identifier, field.as_rule());

            },
            Err(_) => assert!(false)
        }

        // TEST 2
        let attr_access = "v1._field2.f";
        let variable = "v1";
        let field1 = "_field2";
        let field2 = "f";
        
        match SEParser::parse(Rule::attr_accessor, attr_access) {
            Ok(mut pairs) => {
                let pair: Pair<Rule> = pairs.next().unwrap();
                assert_eq!(attr_access, pair.as_str());
                assert_eq!(Rule::attr_accessor, pair.as_rule());
                
                let var_name = pair.clone().into_inner().next().unwrap();
                assert_eq!(variable, var_name.as_str());
                assert_eq!(Rule::rust_identifier, var_name.as_rule());

                let field = pair.clone().into_inner().nth(1).unwrap();
                assert_eq!(field1, field.as_str());
                assert_eq!(Rule::rust_identifier, field.as_rule());

                let field_2 = pair.into_inner().nth(2).unwrap();
                assert_eq!(field2, field_2.as_str());
                assert_eq!(Rule::rust_identifier, field_2.as_rule());

            },
            Err(_) => assert!(false)
        }
    
        // TEST 3
        let attr_access = "_variabl12_oj.hey ";
        let variable = "_variabl12_oj";
        let field1 = "hey";

        match SEParser::parse(Rule::attr_accessor, attr_access) {
            Ok(mut pairs) => {
                let pair: Pair<Rule> = pairs.next().unwrap();
                assert_eq!(attr_access, pair.as_str());
                assert_eq!(Rule::attr_accessor, pair.as_rule());

                let var_name = pair.clone().into_inner().next().unwrap();
                assert_eq!(variable, var_name.as_str());
                assert_eq!(Rule::rust_identifier, var_name.as_rule());

                let field = pair.into_inner().nth(1).unwrap();
                assert_eq!(field1, field.as_str());
                assert_eq!(Rule::rust_identifier, field.as_rule());

            },
            Err(_) => assert!(false)
        }

        assert_error( "we.1var2", Rule::attr_accessor); // not valid
    }


    #[test]
    fn variable() {
        let attr_access = "_variabl12_oj.hey";

        match SEParser::parse(Rule::variable, attr_access) {
            Ok(mut pairs) => {
                let pair: Pair<Rule> = pairs.next().unwrap();
                assert_eq!(attr_access, pair.as_str());
                assert_eq!(Rule::variable, pair.as_rule());

                let attr = pair.clone().into_inner().next().unwrap();
                assert_eq!(attr_access, attr.as_str());
                assert_eq!(Rule::attr_accessor, attr.as_rule());
            },
            Err(_) => assert!(false)
        }

        let rust_id = "_variabl12_oj";

        match SEParser::parse(Rule::variable, rust_id) {
            Ok(mut pairs) => {
                let pair: Pair<Rule> = pairs.next().unwrap();
                assert_eq!(rust_id, pair.as_str());
                assert_eq!(Rule::variable, pair.as_rule());

                let attr = pair.clone().into_inner().next().unwrap();
                assert_eq!(rust_id, attr.as_str());
                assert_eq!(Rule::rust_identifier, attr.as_rule());
            },
            Err(_) => assert!(false)
        }
    }

    #[test]
    fn storage_read() {
        test_parser_f("GET(=AARiYW5rQURNSU4=)", Rule::storage_read, |pair: Pair<Rule>| {
            let key = pair.clone().into_inner().next().unwrap();
            assert_eq!("=AARiYW5rQURNSU4=", key.as_str());
            assert_eq!(Rule::key, key.as_rule());

            let base64 = key.into_inner().next().unwrap();
            assert_eq!("AARiYW5rQURNSU4=", base64.as_str());
            assert_eq!(Rule::base64, base64.as_rule());
        });

        test_parser_f("GET(=AARiYW5r= @ _msg.admin)", Rule::storage_read, |pair: Pair<Rule>| {
            let key = pair.clone().into_inner().next().unwrap();
            assert_eq!("=AARiYW5r= @ _msg.admin", key.as_str());
            assert_eq!(Rule::key, key.as_rule());
            
            let mut inner = key.into_inner();
            let hexa = inner.next().unwrap();
            assert_eq!("AARiYW5r=", hexa.as_str());
            assert_eq!(Rule::base64, hexa.as_rule());

            let expr = inner.next().unwrap();
            assert_eq!("_msg.admin", expr.as_str());
            assert_eq!(Rule::expr, expr.as_rule());
        });
    }


    #[test]
    fn integer() {
        test_parser("1", Rule::int);
        test_parser("152131", Rule::int);
        test_parser("0", Rule::int);

        assert_error( "0123", Rule::int); // not valid
    }

    #[test]
    fn float() {
        test_parser("1.22", Rule::float);
        test_parser("1124.0023", Rule::float);
        test_parser("0.9", Rule::float);

        assert_error("0123", Rule::float);
        assert_error("0.", Rule::float);
    }

    #[test]
    fn expression() {
        test_parser_f("2 + 3", Rule::expr, |pair| {
            
            let int_2 = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("2", int_2.as_str());
            assert_eq!(Rule::int, int_2.as_rule());

            let op_add = pair.clone().into_inner().nth(1).unwrap();
            assert_eq!("+", op_add.as_str());
            assert_eq!(Rule::add, op_add.as_rule());
            
            let int_3 = pair.clone().into_inner().nth(2).unwrap();
            assert_eq!("3", int_3.as_str());
            assert_eq!(Rule::int, int_3.as_rule());
        });          // sum
  
        test_parser_f("2 + (4 - 6)", Rule::expr, |pair| {

            let int_2 = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("2", int_2.as_str());
            assert_eq!(Rule::int, int_2.as_rule());
            
            let op_add = pair.clone().into_inner().nth(1).unwrap();
            assert_eq!("+", op_add.as_str());
            assert_eq!(Rule::add, op_add.as_rule());
            
            let expr = pair.clone().into_inner().nth(2).unwrap();
            assert_eq!("4 - 6", expr.as_str());
            assert_eq!(Rule::expr, expr.as_rule());
        }); // parenthesis
   
        test_parser_f("8 * 4 + 2", Rule::expr, |pair| {

            let int_8 = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("8", int_8.as_str());
            assert_eq!(Rule::int, int_8.as_rule());
            
            let op_mul = pair.clone().into_inner().nth(1).unwrap();
            assert_eq!("*", op_mul.as_str());
            assert_eq!(Rule::mul, op_mul.as_rule());
            
            let int_4 = pair.clone().into_inner().nth(2).unwrap();
            assert_eq!("4", int_4.as_str());
            assert_eq!(Rule::int, int_4.as_rule());

            let op_add = pair.clone().into_inner().nth(3).unwrap();
            assert_eq!("+", op_add.as_str());
            assert_eq!(Rule::add, op_add.as_rule());

            let int_2 = pair.clone().into_inner().nth(4).unwrap();
            assert_eq!("2", int_2.as_str());
            assert_eq!(Rule::int, int_2.as_rule());
        }); // multiplication

        test_parser("8 * 4 + 3^2", Rule::expr);    // power
        test_parser("8 / 4 / 3", Rule::expr);      // division
        test_parser("-2", Rule::expr);             // negation
        test_parser("-2 + -5", Rule::expr);        // negation
        test_parser("-2.44 * -5.23 + (88.23^1.2)", Rule::expr);      // complex expression
   
        test_parser_f("_admin.field1 * -5.23", Rule::expr, |pair| {
            let var_admin = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("_admin.field1 ", var_admin.as_str()); // TODO for some reason comes with space, but the inner rules are fine
            assert_eq!(Rule::variable, var_admin.as_rule());
            
            let op_mul = pair.clone().into_inner().nth(1).unwrap();
            assert_eq!("*", op_mul.as_str());
            assert_eq!(Rule::mul, op_mul.as_rule());
            
            let unary_neg = pair.clone().into_inner().nth(2).unwrap();
            assert_eq!("-", unary_neg.as_str());
            assert_eq!(Rule::neg, unary_neg.as_rule());

            let int_523 = pair.clone().into_inner().nth(3).unwrap();
            assert_eq!("5.23", int_523.as_str());
            assert_eq!(Rule::float, int_523.as_rule());
        }); // expression w/ variables

        test_parser("_admin.field1 * -_var2.yes + (a.b^1.2)", Rule::expr);      
        test_parser("_admin.field1 * -GET(=AARiYW5r= @ admin.f) + (a.b^1.2)", Rule::expr);   // expression w/ storage access
    }

    #[test]
    fn storage_write() {
        test_parser("SET(=AARiYW5rQURNSU4=): 1", Rule::storage_write);
        test_parser("SET(=AARiYW5rQURNSU4=): 1 + ADMIN.FIELD1", Rule::storage_write);
        test_parser("SET(=AARiYW5rQURNSU4=): 1 * (GET(=AARiYW5r= @ admin.yes))", Rule::storage_write);
        test_parser_f("SET(=AARiYW5r= @ pol.pu): (1^3 + -d.a) * (GET(=AARiYW5r= @ admin.yes))", Rule::storage_write, |pair| {
            
            let key = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("=AARiYW5r= @ pol.pu", key.as_str());
            assert_eq!(Rule::key, key.as_rule());
            
            let expr = pair.clone().into_inner().nth(1).unwrap();
            assert_eq!("(1^3 + -d.a) * (GET(=AARiYW5r= @ admin.yes))", expr.as_str());
            assert_eq!(Rule::expr, expr.as_rule());
        });
    }

    #[test]
    fn path_cond_id() {
        test_parser("[PC_2]", Rule::path_cond_id);
        test_parser("[PC_19827]", Rule::path_cond_id);
        test_parser("[PC_0]", Rule::path_cond_id);
    }

    #[test]
    fn pos_branch() {
        test_parser_f("=> [PC_2]", Rule::pos_branches, |pair| {
            let path_cond_id = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("[PC_2]", path_cond_id.as_str());
            assert_eq!(Rule::path_cond_id, path_cond_id.as_rule());
        });

        test_parser_f("=> SET(=AARiYW5rQURNSU4=): 1 * (GET(=AARiYW5r= @ admin.yes))", Rule::pos_branches, |pair| {
            let storage_write = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("SET(=AARiYW5rQURNSU4=): 1 * (GET(=AARiYW5r= @ admin.yes))", storage_write.as_str());
            assert_eq!(Rule::storage_write, storage_write.as_rule());
        });

        test_parser("=> None", Rule::pos_branches);
    }


    #[test]
    fn neg_branch() {
        test_parser_f("<- [PC_2]", Rule::neg_branches, |pair| {
            let path_cond_id = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("[PC_2]", path_cond_id.as_str());
            assert_eq!(Rule::path_cond_id, path_cond_id.as_rule());
        });

        test_parser_f("<- SET(=AARiYW5rQURNSU4=): 1 * (GET(=AARiYW5r= @ admin.yes))", Rule::neg_branches, |pair| {
            let storage_write = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("SET(=AARiYW5rQURNSU4=): 1 * (GET(=AARiYW5r= @ admin.yes))", storage_write.as_str());
            assert_eq!(Rule::storage_write, storage_write.as_rule());
        });

        test_parser_f("<- SET(=AARiYW5r= @ admin.yes): GET(=AARiYW5r= @ lala.no) + 1", Rule::neg_branches, |pair| {
            let storage_write = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("SET(=AARiYW5r= @ admin.yes): GET(=AARiYW5r= @ lala.no) + 1", storage_write.as_str());
            assert_eq!(Rule::storage_write, storage_write.as_rule());
        });

        

        test_parser("<- None", Rule::neg_branches);
    }

    #[test]
    fn rel_operator() {
        test_parser(">=", Rule::gte);
        test_parser("<=", Rule::lte);
        test_parser("==", Rule::equal);
        test_parser("!=", Rule::ne);
        test_parser("<", Rule::lt);
        test_parser(">", Rule::gt);
    }

    #[test]
    fn infix() {
        test_parser("+", Rule::add);
        test_parser("-", Rule::sub);
        test_parser("*", Rule::mul);
        test_parser("/", Rule::div);
        test_parser("^", Rule::pow);
    }

    #[test]
    fn bool_expr() {
        test_parser_f("1 < 3", Rule::bool_expr, |pair| {
            let pair = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("1 < 3", pair.as_str());
            assert_eq!(Rule::rel_expr, pair.as_rule());

            let pair = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("1 < 3", pair.as_str());
            assert_eq!(Rule::comparison, pair.as_rule());

            let expr1 = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("1 ", expr1.as_str()); // TODO includes the space, but inner rules are fine
            assert_eq!(Rule::expr, expr1.as_rule());

            let lt = pair.clone().into_inner().nth(1).unwrap();
            assert_eq!("<", lt.as_str());
            assert_eq!(Rule::lt, lt.as_rule());

            let expr2 = pair.clone().into_inner().nth(2).unwrap();
            assert_eq!("3", expr2.as_str());
            assert_eq!(Rule::expr, expr2.as_rule());
        });

        test_parser_f("(GET(=AARiYW5r= @ admin.yes)) >= 3.23", Rule::bool_expr, |pair| {
            let pair = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("(GET(=AARiYW5r= @ admin.yes)) >= 3.23", pair.as_str());
            assert_eq!(Rule::rel_expr, pair.as_rule());

            let pair = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("(GET(=AARiYW5r= @ admin.yes)) >= 3.23", pair.as_str());
            assert_eq!(Rule::comparison, pair.as_rule());

            let expr1 = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("(GET(=AARiYW5r= @ admin.yes)) ", expr1.as_str()); // TODO includes the space, but inner rules are fine
            assert_eq!(Rule::expr, expr1.as_rule());

            let gte = pair.clone().into_inner().nth(1).unwrap();
            assert_eq!(">=", gte.as_str());
            assert_eq!(Rule::gte, gte.as_rule());

            let expr2 = pair.clone().into_inner().nth(2).unwrap();
            assert_eq!("3.23", expr2.as_str());
            assert_eq!(Rule::expr, expr2.as_rule());
        });

        test_parser_f("True", Rule::bool_expr, |pair| {
            let pair = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("True", pair.as_str());
            assert_eq!(Rule::always_true, pair.as_rule());
        });

        test_parser_f("Type(msg) == BlaBla", Rule::bool_expr, |pair| {
            let pair = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("Type(msg) == BlaBla", pair.as_str());
            assert_eq!(Rule::rel_expr, pair.as_rule());

            let pair = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("Type(msg) == BlaBla", pair.as_str());
            assert_eq!(Rule::type_checking, pair.as_rule());

            let lhs = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("msg", lhs.as_str());
            assert_eq!(Rule::variable, lhs.as_rule());

            let op = pair.clone().into_inner().nth(1).unwrap();
            assert_eq!("==", op.as_str());
            assert_eq!(Rule::equal, op.as_rule());

            let rhs = pair.clone().into_inner().nth(2).unwrap();
            assert_eq!("BlaBla", rhs.as_str());
            assert_eq!(Rule::rust_identifier, rhs.as_rule());
        });

        test_parser_f("Type(msg) != BlaBla", Rule::bool_expr, |pair| {
            let pair = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("Type(msg) != BlaBla", pair.as_str());
            assert_eq!(Rule::rel_expr, pair.as_rule());

            let pair = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("Type(msg) != BlaBla", pair.as_str());
            assert_eq!(Rule::type_checking, pair.as_rule());

            let lhs = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("msg", lhs.as_str());
            assert_eq!(Rule::variable, lhs.as_rule());

            let op = pair.clone().into_inner().nth(1).unwrap();
            assert_eq!("!=", op.as_str());
            assert_eq!(Rule::ne, op.as_rule());

            let rhs = pair.clone().into_inner().nth(2).unwrap();
            assert_eq!("BlaBla", rhs.as_str());
            assert_eq!(Rule::rust_identifier, rhs.as_rule());
        });
    }

    #[test]
    fn path_cond() {
        test_parser_f("[PC_2] _msg.type == AddOne", Rule::path_cond, |pair| {
            
            let path_cond_id = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("[PC_2]", path_cond_id.as_str());
            assert_eq!(Rule::path_cond_id, path_cond_id.as_rule());

            let bool_expr = pair.clone().into_inner().nth(1).unwrap();
            assert_eq!("_msg.type == AddOne", bool_expr.as_str());
            assert_eq!(Rule::bool_expr, bool_expr.as_rule());
        });

        test_parser("[PC_1] True", Rule::path_cond);
    }

    #[test]
    fn path_cond_node() {
        test_parser_f("[PC_1] _msg.type == AddOne
=> [PC_2]
<- SET(=AARiYW5rQURNSU4=): GET(=AARiYW5rQURNSU4=) + 1
<- SET(=AARiYW5r= @ admin.yes): GET(=AARiYW5r= @ lala.no) + 1", 
        Rule::path_cond_node, |pair| {
            
            let path_cond = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("[PC_1] _msg.type == AddOne\n", path_cond.as_str());
            assert_eq!(Rule::path_cond, path_cond.as_rule());

            let pos_branch = pair.clone().into_inner().nth(1).unwrap();
            assert_eq!("=> [PC_2]\n", pos_branch.as_str());
            assert_eq!(Rule::pos_branches, pos_branch.as_rule());

            let pair = pair.clone().into_inner().nth(2).unwrap();
            assert_eq!("<- SET(=AARiYW5rQURNSU4=): GET(=AARiYW5rQURNSU4=) + 1\n<- SET(=AARiYW5r= @ admin.yes): GET(=AARiYW5r= @ lala.no) + 1", pair.as_str());
            assert_eq!(Rule::neg_branches, pair.as_rule());

            let neg_branch1 = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("SET(=AARiYW5rQURNSU4=): GET(=AARiYW5rQURNSU4=) + 1", neg_branch1.as_str());
            assert_eq!(Rule::storage_write, neg_branch1.as_rule());

            let neg_branch2 = pair.clone().into_inner().nth(1).unwrap();
            assert_eq!("SET(=AARiYW5r= @ admin.yes): GET(=AARiYW5r= @ lala.no) + 1", neg_branch2.as_str());
            assert_eq!(Rule::storage_write, neg_branch2.as_rule());
        });
    }

    #[test]
    fn types() {
        test_parser("string", Rule::string_t);
        test_parser("int", Rule::int_t);
        test_parser("float", Rule::float_t);
    }

    #[test]
    fn subtype_defs() {
        test_parser_f("- from: string", 
        Rule::subtype_def, |pair| {

            let rust_identifier = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("from", rust_identifier.as_str());
            assert_eq!(Rule::rust_identifier, rust_identifier.as_rule());

            let offset = pair.clone().into_inner().nth(1).unwrap();
            assert_eq!("string", offset.as_str());
            assert_eq!(Rule::string_t, offset.as_rule());
        });

        test_parser("- to: int", Rule::subtype_def);
    }

    #[test]
    fn attr_offset() {
        test_parser_f("> Transfer:
        - from: string
        - to: string",
        Rule::attr_def, |pair| {

            let rust_identifier = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("Transfer", rust_identifier.as_str());
            assert_eq!(Rule::rust_identifier, rust_identifier.as_rule());

            let offset_definition = pair.clone().into_inner().nth(1).unwrap();
            assert_eq!("- from: string", offset_definition.as_str());
            assert_eq!(Rule::subtype_def, offset_definition.as_rule());

            let offset_definition = pair.clone().into_inner().nth(2).unwrap();
            assert_eq!("- to: string", offset_definition.as_str());
            assert_eq!(Rule::subtype_def, offset_definition.as_rule());
        });
    }

    #[test]
    fn input() {
        test_parser_f("_msg: ExecuteMsg",
        Rule::input, |pair| {

            let rust_identifier = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("_msg", rust_identifier.as_str());
            assert_eq!(Rule::rust_identifier, rust_identifier.as_rule());

            let input_type = pair.clone().into_inner().nth(1).unwrap();
            assert_eq!("ExecuteMsg", input_type.as_str());
            assert_eq!(Rule::custom, input_type.as_rule());

        });
    }


    #[test]
    fn header() {
        test_parser_f("I ----------------------------",
        Rule::header, |pair| {

            let instantiate = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("I", instantiate.as_str());
            assert_eq!(Rule::instantiate, instantiate.as_rule());

        });
    }

    #[test]
    fn custom_type_def() {
        test_parser("> AddUser:
    - admin: string
> AddOne:
> Transfer:
    - from: string
    - to: string", 
    Rule::attr_defs)

    }



    #[test]
    fn section() {
        test_parser_f("I ----------------------------
_deps: DepsMut
_env: Env
_info: MessageInfo
_msg: ExecuteMsg
> AddUser:
    - admin: string
> AddOne:
> Transfer:
    - from: string
    - to: string


[PC_1] _msg.type == AddUser
=> [PC_2]
<- [PC_3]

[PC_2] GET(=AARiYW5r= @ _msg.admin) == null
=> SET(=AARiYW5r= @ _msg.admin): 100
<- None

[PC_3] _msg.type == AddOne
=> SET(=AARiYW5rQURNSU4=): GET(=AARiYW5rQURNSU4=) + 1
<- [PC_4]

[PC_4] _msg.type == Transfer
=> None
<- None", Rule::section, |pair| {

            let header = pair.clone().into_inner().nth(0).unwrap();
            assert_eq!("I ----------------------------", header.as_str());
            assert_eq!(Rule::header, header.as_rule());

            let inputs = pair.clone().into_inner().nth(1).unwrap();
            assert_eq!("_deps: DepsMut
_env: Env
_info: MessageInfo
_msg: ExecuteMsg", inputs.as_str());
            assert_eq!(Rule::inputs, inputs.as_rule());

            let attr_offsets = pair.clone().into_inner().nth(2).unwrap();
            assert_eq!("> AddUser:
    - admin: string
> AddOne:
> Transfer:
    - from: string
    - to: string", attr_offsets.as_str());
            assert_eq!(Rule::attr_defs, attr_offsets.as_rule());

            let path_cond_nodes = pair.clone().into_inner().nth(3).unwrap();
            assert_eq!("[PC_1] _msg.type == AddUser
=> [PC_2]
<- [PC_3]

[PC_2] GET(=AARiYW5r= @ _msg.admin) == null
=> SET(=AARiYW5r= @ _msg.admin): 100
<- None

[PC_3] _msg.type == AddOne
=> SET(=AARiYW5rQURNSU4=): GET(=AARiYW5rQURNSU4=) + 1
<- [PC_4]

[PC_4] _msg.type == Transfer
=> None
<- None",   path_cond_nodes.as_str());
            assert_eq!(Rule::path_cond_nodes, path_cond_nodes.as_rule());

        });

            
    }



}