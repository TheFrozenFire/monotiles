use ark_ff::Field;
use core::ops::{Add, Mul};

/// Dense matrix over an arkworks Field.
///
/// Stored in row-major order: data[i * cols + j] is the element at row i, column j.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Matrix<F: Field> {
    pub rows: usize,
    pub cols: usize,
    pub data: Vec<F>,
}

impl<F: Field> Matrix<F> {
    pub fn new(rows: usize, cols: usize, data: Vec<F>) -> Self {
        assert_eq!(data.len(), rows * cols, "data length must equal rows * cols");
        Self { rows, cols, data }
    }

    pub fn zeros(rows: usize, cols: usize) -> Self {
        Self {
            rows,
            cols,
            data: vec![F::ZERO; rows * cols],
        }
    }

    pub fn identity(n: usize) -> Self {
        let mut m = Self::zeros(n, n);
        for i in 0..n {
            m[(i, i)] = F::ONE;
        }
        m
    }

    /// Create a matrix from a 2D array of field elements.
    pub fn from_rows(rows: &[&[F]]) -> Self {
        assert!(!rows.is_empty());
        let n_cols = rows[0].len();
        assert!(rows.iter().all(|r| r.len() == n_cols));
        let data: Vec<F> = rows.iter().flat_map(|r| r.iter().copied()).collect();
        Self::new(rows.len(), n_cols, data)
    }

    pub fn get(&self, row: usize, col: usize) -> F {
        self.data[row * self.cols + col]
    }

    pub fn set(&mut self, row: usize, col: usize, val: F) {
        self.data[row * self.cols + col] = val;
    }

    pub fn transpose(&self) -> Self {
        let mut result = Self::zeros(self.cols, self.rows);
        for i in 0..self.rows {
            for j in 0..self.cols {
                result[(j, i)] = self[(i, j)];
            }
        }
        result
    }

    /// Matrix multiplication. Panics if dimensions are incompatible.
    pub fn mul(&self, other: &Self) -> Self {
        assert_eq!(
            self.cols, other.rows,
            "incompatible dimensions for multiplication: {}x{} * {}x{}",
            self.rows, self.cols, other.rows, other.cols
        );
        let mut result = Self::zeros(self.rows, other.cols);
        for i in 0..self.rows {
            for k in 0..self.cols {
                let a = self[(i, k)];
                if a == F::ZERO {
                    continue;
                }
                for j in 0..other.cols {
                    result[(i, j)] += a * other[(k, j)];
                }
            }
        }
        result
    }

    /// Scalar multiplication.
    pub fn scale(&self, scalar: F) -> Self {
        Self {
            rows: self.rows,
            cols: self.cols,
            data: self.data.iter().map(|&x| x * scalar).collect(),
        }
    }

    /// Determinant (square matrices only). Uses Bareiss-like elimination.
    pub fn determinant(&self) -> F {
        assert_eq!(self.rows, self.cols, "determinant requires square matrix");
        let n = self.rows;
        if n == 0 {
            return F::ONE;
        }
        if n == 1 {
            return self[(0, 0)];
        }
        if n == 2 {
            return self[(0, 0)] * self[(1, 1)] - self[(0, 1)] * self[(1, 0)];
        }

        // Gaussian elimination with partial pivoting
        let mut m = self.clone();
        let mut det = F::ONE;
        let mut sign = F::ONE;

        for col in 0..n {
            // Find pivot
            let pivot_row = (col..n).find(|&r| m[(r, col)] != F::ZERO);
            let pivot_row = match pivot_row {
                Some(r) => r,
                None => return F::ZERO,
            };

            if pivot_row != col {
                // Swap rows
                for j in 0..n {
                    let tmp = m[(col, j)];
                    m[(col, j)] = m[(pivot_row, j)];
                    m[(pivot_row, j)] = tmp;
                }
                sign = -sign;
            }

            let pivot = m[(col, col)];
            det *= pivot;
            let pivot_inv = pivot.inverse().unwrap();

            for i in (col + 1)..n {
                let factor = m[(i, col)] * pivot_inv;
                m[(i, col)] = F::ZERO;
                for j in (col + 1)..n {
                    let sub = factor * m[(col, j)];
                    m[(i, j)] -= sub;
                }
            }
        }

        det * sign
    }

    /// Compute the trace (sum of diagonal elements).
    pub fn trace(&self) -> F {
        assert_eq!(self.rows, self.cols, "trace requires square matrix");
        (0..self.rows).map(|i| self[(i, i)]).sum()
    }

    /// Matrix exponentiation by repeated squaring.
    pub fn pow(&self, mut exp: u64) -> Self {
        assert_eq!(self.rows, self.cols, "pow requires square matrix");
        let mut result = Self::identity(self.rows);
        let mut base = self.clone();
        while exp > 0 {
            if exp & 1 == 1 {
                result = result.mul(&base);
            }
            base = base.mul(&base);
            exp >>= 1;
        }
        result
    }
}

impl<F: Field> core::ops::Index<(usize, usize)> for Matrix<F> {
    type Output = F;
    fn index(&self, (row, col): (usize, usize)) -> &F {
        &self.data[row * self.cols + col]
    }
}

impl<F: Field> core::ops::IndexMut<(usize, usize)> for Matrix<F> {
    fn index_mut(&mut self, (row, col): (usize, usize)) -> &mut F {
        &mut self.data[row * self.cols + col]
    }
}

impl<F: Field> Add for &Matrix<F> {
    type Output = Matrix<F>;
    fn add(self, other: Self) -> Matrix<F> {
        assert_eq!(self.rows, other.rows);
        assert_eq!(self.cols, other.cols);
        Matrix {
            rows: self.rows,
            cols: self.cols,
            data: self
                .data
                .iter()
                .zip(other.data.iter())
                .map(|(&a, &b)| a + b)
                .collect(),
        }
    }
}

impl<F: Field> Mul for &Matrix<F> {
    type Output = Matrix<F>;
    fn mul(self, other: Self) -> Matrix<F> {
        self.mul(other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fields::FrSqrt5;
    use ark_bls12_381::Fr;
    use ark_ff::{AdditiveGroup, Field};

    type F = Fr;

    #[test]
    fn identity_times_identity() {
        let id = Matrix::<F>::identity(3);
        assert_eq!(id.mul(&id), id);
    }

    #[test]
    fn identity_determinant_is_one() {
        let id = Matrix::<F>::identity(4);
        assert_eq!(id.determinant(), F::ONE);
    }

    #[test]
    fn two_by_two_determinant() {
        let m = Matrix::<F>::new(
            2,
            2,
            vec![
                F::from(3u64),
                F::from(8u64),
                F::from(4u64),
                F::from(6u64),
            ],
        );
        // det = 3*6 - 8*4 = 18 - 32 = -14
        let expected = -F::from(14u64);
        assert_eq!(m.determinant(), expected);
    }

    #[test]
    fn transpose_involution() {
        let m = Matrix::<F>::new(
            2,
            3,
            vec![
                F::from(1u64),
                F::from(2u64),
                F::from(3u64),
                F::from(4u64),
                F::from(5u64),
                F::from(6u64),
            ],
        );
        assert_eq!(m.transpose().transpose(), m);
    }

    #[test]
    fn matrix_mul_dimensions() {
        let a = Matrix::<F>::zeros(2, 3);
        let b = Matrix::<F>::zeros(3, 4);
        let c = a.mul(&b);
        assert_eq!(c.rows, 2);
        assert_eq!(c.cols, 4);
    }

    #[test]
    fn mul_associativity() {
        let a = Matrix::<F>::new(
            2,
            2,
            vec![
                F::from(1u64),
                F::from(2u64),
                F::from(3u64),
                F::from(4u64),
            ],
        );
        let b = Matrix::<F>::new(
            2,
            2,
            vec![
                F::from(5u64),
                F::from(6u64),
                F::from(7u64),
                F::from(8u64),
            ],
        );
        let c = Matrix::<F>::new(
            2,
            2,
            vec![
                F::from(9u64),
                F::from(10u64),
                F::from(11u64),
                F::from(12u64),
            ],
        );
        assert_eq!(a.mul(&b).mul(&c), a.mul(&b.mul(&c)));
    }

    #[test]
    fn singular_matrix_determinant_zero() {
        // Row 2 = 2 * Row 1
        let m = Matrix::<F>::new(
            2,
            2,
            vec![
                F::from(1u64),
                F::from(2u64),
                F::from(2u64),
                F::from(4u64),
            ],
        );
        assert_eq!(m.determinant(), F::ZERO);
    }

    #[test]
    fn matrix_pow_zero_is_identity() {
        let m = Matrix::<F>::new(
            2,
            2,
            vec![
                F::from(3u64),
                F::from(1u64),
                F::from(0u64),
                F::from(2u64),
            ],
        );
        assert_eq!(m.pow(0), Matrix::<F>::identity(2));
    }

    #[test]
    fn matrix_pow_consistent_with_mul() {
        let m = Matrix::<F>::new(
            2,
            2,
            vec![
                F::from(1u64),
                F::from(1u64),
                F::from(1u64),
                F::from(0u64),
            ],
        );
        assert_eq!(m.pow(3), m.mul(&m).mul(&m));
    }

    #[test]
    fn trace_of_identity() {
        let id = Matrix::<F>::identity(5);
        assert_eq!(id.trace(), F::from(5u64));
    }

    #[test]
    fn matrix_over_extension_field() {
        let one = FrSqrt5::ONE;
        let zero = FrSqrt5::ZERO;
        let id = Matrix::<FrSqrt5>::identity(2);
        let m = Matrix::new(2, 2, vec![one + one, zero, one, one]);
        let result = id.mul(&m);
        assert_eq!(result, m);
    }
}
