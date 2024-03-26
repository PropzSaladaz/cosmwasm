use super::super::parser::nodes::*;
use std::ops;

/// Define an implementation for all arithmetic operations, with automaic conversion
/// between types
macro_rules! impl_arithmetic_operations {
    ($op_name:ident, $fn_name:ident, $op:tt) => {
        impl ops::$op_name for Number {
            type Output = Number;

            fn $fn_name(self, other: Number) -> Self::Output {
                match (self, other) {
                    (Number::Int(a), Number::Int(b))     => Number::Int( a $op b ),
                    (Number::Int(a), Number::Float(b))   => Number::Float( (a as Float) $op b ),
                    (Number::Float(a), Number::Int(b))   => Number::Float( a $op (b as Float) ),
                    (Number::Float(a), Number::Float(b)) => Number::Float( a $op b ),
                }
            }
        }
    }
}

impl_arithmetic_operations!(Add, add, +);
impl_arithmetic_operations!(Sub, sub, -);
impl_arithmetic_operations!(Mul, mul, *);
impl_arithmetic_operations!(Div, div, /);

impl PartialEq for Number {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Number::Int(a), Number::Int(b))     => a == b,
            (Number::Int(a), Number::Float(b))   => (*a as Float) == *b,
            (Number::Float(a), Number::Int(b))   => *a == (*b as Float),
            (Number::Float(a), Number::Float(b)) => a == b
        }
    }
}

impl PartialOrd for Number {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Number::Int(a), Number::Int(b))     => Some(a.cmp(b)),
            (Number::Int(a), Number::Float(b))   => (*a as Float).partial_cmp(b),
            (Number::Float(a), Number::Int(b))   => a.partial_cmp(&(*b as Float)),
            (Number::Float(a), Number::Float(b)) => a.partial_cmp(b)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn number_arithmetic_sum() {
        let a = Number::Int(3);
        let b = Number::Int(2);

        assert_eq!(a+b, Number::Int(5));

        let a = Number::Float(3.2);
        let b = Number::Float(1.5);

        assert_eq!(a+b, Number::Float(4.7));

        let a = Number::Int(3);
        let b = Number::Float(2.5);

        assert_eq!(a+b, Number::Float(5.5));

        let a = Number::Int(3);
        let b = Number::Float(2.5);

        assert_eq!(b+a, Number::Float(5.5));

    }

    #[test]
    fn number_arithmetic_sub() {
        let a = Number::Int(3);
        let b = Number::Int(2);

        assert_eq!(a-b, Number::Int(1));

        let a = Number::Float(3.2);
        let b = Number::Float(1.5);

        assert_eq!(a-b, Number::Float(1.7));

        let a = Number::Int(3);
        let b = Number::Float(2.5);

        assert_eq!(a-b, Number::Float(0.5));

        let a = Number::Int(1);
        let b = Number::Float(3.5);
        
        assert_eq!(b-a, Number::Float(2.5));
    }

    #[test]
    fn number_arithmetic_mul() {
        let a = Number::Int(3);
        let b = Number::Int(2);

        assert_eq!(a*b, Number::Int(6));

        let a = Number::Float(3.2);
        let b = Number::Float(1.5);

        assert_eq!(a*b, Number::Float(4.8));

        let a = Number::Int(3);
        let b = Number::Float(2.5);

        assert_eq!(a*b, Number::Float(7.5));

        let a = Number::Int(3);
        let b = Number::Float(2.5);

        assert_eq!(a*b, Number::Float(7.5));
    }

    #[test]
    fn number_arithmetic_div() {
        let a = Number::Int(3);
        let b = Number::Int(2);

        assert_eq!(a/b, Number::Int(1));

        let a = Number::Float(8.0);
        let b = Number::Float(2.5);

        assert_eq!(a/b, Number::Float(3.2));

        let a = Number::Int(8);
        let b = Number::Float(2.5);

        assert_eq!(a/b, Number::Float(3.2));

        let a = Number::Int(2);
        let b = Number::Float(8.6);

        assert_eq!(b/a, Number::Float(4.3));
    }

    #[test]
    fn number_rel_op() {
        assert!(Number::Int(3) > Number::Int(1));
        assert!(Number::Int(0) < Number::Int(1));
        assert!(Number::Int(1) <= Number::Int(1));
        assert!(Number::Int(1) != Number::Int(2));

        assert!(Number::Float(3.0) > Number::Float(1.0));
        assert!(Number::Float(0.0) < Number::Float(1.0));
        assert!(Number::Float(1.0) <= Number::Float(1.0));
        assert!(Number::Float(1.0) != Number::Float(2.0));

        assert!(Number::Int(3) > Number::Float(2.95));
        assert!(Number::Int(0) < Number::Float(1.0));
        assert!(Number::Int(1) <= Number::Float(1.0));
        assert!(Number::Int(1) != Number::Float(2.0));
    }
}