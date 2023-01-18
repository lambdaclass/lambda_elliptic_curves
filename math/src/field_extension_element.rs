use crate::config::{ORDER_FIELD_EXTENSION, ORDER_P};
use crate::{field_element::FieldElement, polynomial::Polynomial};
use std::ops;

type FE = FieldElement<ORDER_P>;

/// Represents an element in an extension of a prime field
/// as polynomials modulo a defining polynomial.
#[derive(Debug, Clone)]
pub struct FieldExtensionElement {
    value: Polynomial<ORDER_P>,
}

impl FieldExtensionElement {
    /// Creates a `FieldExtensionElement` from a polynomial `p`.
    /// It keeps the remainder of dividing `p` by the defining polynomial.
    pub fn new(p: Polynomial<ORDER_P>) -> Self {
        let (_quotient, remainder) = p.long_division_with_remainder(&Self::defining_polynomial());
        Self { value: remainder }
    }

    /// Creates a `FieldExtensionElement` belonging to the base prime field.
    pub fn new_base(value: u128) -> Self {
        Self::new(Polynomial::new_monomial(FE::new(value), 0))
    }

    /// Returns the defining polynomial of the field. In this case:
    ///     1 + X^2
    ///
    /// This polynomial is chosen this way because the resulting field extension
    /// is of degree 2. With this property a type I pairing compatible elliptic curve
    /// is then defined.
    pub fn defining_polynomial() -> Polynomial<ORDER_P> {
        Polynomial::new(vec![FE::new(1), FE::new(0), FE::new(1)])
    }

    /// Returns `self` to the power of `exponent` using
    /// right-to-left binary method for modular exponentiation.
    pub fn pow(&self, mut exponent: u128) -> Self {
        let mut result = Self::new(Polynomial::new_monomial(FE::new(1), 0));
        let mut base = self.clone();

        while exponent > 0 {
            // exponent % 2 == 1
            if exponent & 1 == 1 {
                result = &result * &base;
            }
            // exponent = exponent / 2
            exponent >>= 1;
            base = &base * &base;
        }
        result
    }

    pub fn inv(self) -> Self {
        assert_ne!(
            self.value,
            Polynomial::zero(),
            "Cannot invert the zero element."
        );
        self.pow(ORDER_FIELD_EXTENSION - 2)
    }
}

impl PartialEq for FieldExtensionElement {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}
impl Eq for FieldExtensionElement {}

impl ops::Add<&FieldExtensionElement> for &FieldExtensionElement {
    type Output = FieldExtensionElement;

    fn add(self, a_field_element: &FieldExtensionElement) -> Self::Output {
        Self::Output {
            value: &a_field_element.value + &self.value,
        }
    }
}

impl ops::Add<FieldExtensionElement> for FieldExtensionElement {
    type Output = FieldExtensionElement;

    fn add(self, a_field_element: FieldExtensionElement) -> Self::Output {
        &self + &a_field_element
    }
}

impl ops::Add<&FieldExtensionElement> for FieldExtensionElement {
    type Output = FieldExtensionElement;

    fn add(self, a_field_element: &FieldExtensionElement) -> Self::Output {
        &self + a_field_element
    }
}

impl ops::Add<FieldExtensionElement> for &FieldExtensionElement {
    type Output = FieldExtensionElement;

    fn add(self, a_field_element: FieldExtensionElement) -> Self::Output {
        self + &a_field_element
    }
}

impl ops::Neg for &FieldExtensionElement {
    type Output = FieldExtensionElement;

    fn neg(self) -> Self::Output {
        Self::Output {
            value: -self.value.clone(),
        }
    }
}

impl ops::Neg for FieldExtensionElement {
    type Output = FieldExtensionElement;

    fn neg(self) -> Self::Output {
        -&self
    }
}

impl ops::Sub<&FieldExtensionElement> for &FieldExtensionElement {
    type Output = FieldExtensionElement;

    fn sub(self, substrahend: &FieldExtensionElement) -> Self::Output {
        self + &(-substrahend)
    }
}

impl ops::Sub<FieldExtensionElement> for FieldExtensionElement {
    type Output = FieldExtensionElement;

    fn sub(self, substrahend: FieldExtensionElement) -> Self::Output {
        &self - &substrahend
    }
}

impl ops::Sub<&FieldExtensionElement> for FieldExtensionElement {
    type Output = FieldExtensionElement;

    fn sub(self, substrahend: &FieldExtensionElement) -> Self::Output {
        &self - substrahend
    }
}

impl ops::Sub<FieldExtensionElement> for &FieldExtensionElement {
    type Output = FieldExtensionElement;

    fn sub(self, substrahend: FieldExtensionElement) -> Self::Output {
        self - &substrahend
    }
}

impl ops::Mul<&FieldExtensionElement> for &FieldExtensionElement {
    type Output = FieldExtensionElement;

    fn mul(self, a_field_extension_element: &FieldExtensionElement) -> Self::Output {
        let p = self.value.mul_with_ref(&a_field_extension_element.value);
        Self::Output::new(p)
    }
}

impl ops::Mul<FieldExtensionElement> for FieldExtensionElement {
    type Output = FieldExtensionElement;

    fn mul(self, a_field_extension_element: FieldExtensionElement) -> Self::Output {
        &self * &a_field_extension_element
    }
}

impl ops::Mul<&FieldExtensionElement> for FieldExtensionElement {
    type Output = FieldExtensionElement;

    fn mul(self, a_field_extension_element: &FieldExtensionElement) -> Self::Output {
        &self * a_field_extension_element
    }
}

impl ops::Mul<FieldExtensionElement> for &FieldExtensionElement {
    type Output = FieldExtensionElement;

    fn mul(self, a_field_extension_element: FieldExtensionElement) -> Self::Output {
        self * &a_field_extension_element
    }
}

impl ops::Div<&FieldExtensionElement> for &FieldExtensionElement {
    type Output = FieldExtensionElement;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, dividend: &FieldExtensionElement) -> Self::Output {
        self * &dividend.clone().inv()
    }
}

impl ops::Div<FieldExtensionElement> for FieldExtensionElement {
    type Output = FieldExtensionElement;

    fn div(self, dividend: FieldExtensionElement) -> Self::Output {
        &self / &dividend
    }
}

impl ops::Div<FieldExtensionElement> for &FieldExtensionElement {
    type Output = FieldExtensionElement;

    fn div(self, dividend: FieldExtensionElement) -> Self::Output {
        self / &dividend
    }
}

impl ops::Div<&FieldExtensionElement> for FieldExtensionElement {
    type Output = FieldExtensionElement;

    fn div(self, dividend: &FieldExtensionElement) -> Self::Output {
        &self / dividend
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[allow(clippy::upper_case_acronyms)]
    type FEE = FieldExtensionElement;

    #[test]
    fn test_creating_a_field_element_extension_gets_the_remainder_of_the_polynomial() {
        let a = FEE::new(Polynomial::new(vec![
            FE::new(2),
            FE::new(3),
            FE::new(0),
            FE::new(1),
        ]));
        let expected_result = FEE::new(Polynomial::new(vec![FE::new(2), FE::new(2)]));
        assert_eq!(a, expected_result);
    }

    #[test]
    fn test_add_1() {
        let a = FEE::new(Polynomial::new(vec![FE::new(0), FE::new(3)]));
        let b = FEE::new(Polynomial::new(vec![-FE::new(2), FE::new(8)]));
        let expected_result = FEE::new(Polynomial::new(vec![FE::new(57), FE::new(11)]));
        assert_eq!(a + b, expected_result);
    }

    #[test]
    fn test_add_2() {
        let a = FEE::new(Polynomial::new(vec![FE::new(12), FE::new(5)]));
        let b = FEE::new(Polynomial::new(vec![-FE::new(4), FE::new(2)]));
        let expected_result = FEE::new(Polynomial::new(vec![FE::new(8), FE::new(7)]));
        assert_eq!(a + b, expected_result);
    }

    #[test]
    fn test_sub_1() {
        let a = FEE::new(Polynomial::new(vec![FE::new(0), FE::new(3)]));
        let b = FEE::new(Polynomial::new(vec![-FE::new(2), FE::new(8)]));
        let expected_result = FEE::new(Polynomial::new(vec![FE::new(2), FE::new(54)]));
        assert_eq!(a - b, expected_result);
    }

    #[test]
    fn test_sub_2() {
        let a = FEE::new(Polynomial::new(vec![FE::new(12), FE::new(5)]));
        let b = FEE::new(Polynomial::new(vec![-FE::new(4), FE::new(2)]));
        let expected_result = FEE::new(Polynomial::new(vec![FE::new(16), FE::new(3)]));
        assert_eq!(a - b, expected_result);
    }

    #[test]
    fn test_mul_1() {
        let a = FEE::new(Polynomial::new(vec![FE::new(0), FE::new(3)]));
        let b = FEE::new(Polynomial::new(vec![-FE::new(2), FE::new(8)]));
        let expected_result = FEE::new(Polynomial::new(vec![FE::new(35), FE::new(53)]));
        assert_eq!(a * b, expected_result);
    }

    #[test]
    fn test_mul_2() {
        let a = FEE::new(Polynomial::new(vec![FE::new(12), FE::new(5)]));
        let b = FEE::new(Polynomial::new(vec![-FE::new(4), FE::new(2)]));
        let expected_result = FEE::new(Polynomial::new(vec![FE::new(1), FE::new(4)]));
        assert_eq!(a * b, expected_result);
    }

    #[test]
    fn test_div_1() {
        let a = FEE::new(Polynomial::new(vec![FE::new(0), FE::new(3)]));
        let b = FEE::new(Polynomial::new(vec![-FE::new(2), FE::new(8)]));
        let expected_result = FEE::new(Polynomial::new(vec![FE::new(42), FE::new(19)]));
        assert_eq!(a / b, expected_result);
    }

    #[test]
    fn test_div_2() {
        let a = FEE::new(Polynomial::new(vec![FE::new(12), FE::new(5)]));
        let b = FEE::new(Polynomial::new(vec![-FE::new(4), FE::new(2)]));
        let expected_result = FEE::new(Polynomial::new(vec![FE::new(4), FE::new(45)]));
        assert_eq!(a / b, expected_result);
    }

    #[test]
    fn test_pow_1() {
        let a = FEE::new(Polynomial::new(vec![FE::new(0), FE::new(3)]));
        let b = 5;
        let expected_result = FEE::new(Polynomial::new(vec![FE::new(0), FE::new(7)]));
        assert_eq!(a.pow(b), expected_result);
    }

    #[test]
    fn test_pow_2() {
        let a = FEE::new(Polynomial::new(vec![FE::new(12), FE::new(5)]));
        let b = 8;
        let expected_result = FEE::new(Polynomial::new(vec![FE::new(52), FE::new(35)]));
        assert_eq!(a.pow(b), expected_result);
    }

    #[test]
    fn test_inv_1() {
        let a = FEE::new(Polynomial::new(vec![FE::new(0), FE::new(3)]));
        let expected_result = FEE::new(Polynomial::new(vec![FE::new(0), FE::new(39)]));
        assert_eq!(a.inv(), expected_result);
    }

    #[test]
    fn test_inv() {
        let a = FEE::new(Polynomial::new(vec![FE::new(12), FE::new(5)]));
        let expected_result = FEE::new(Polynomial::new(vec![FE::new(28), FE::new(8)]));
        assert_eq!(a.inv(), expected_result);
    }
}
