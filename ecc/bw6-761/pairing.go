// Copyright 2020 ConsenSys AG
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package bw6761

import (
	"errors"

	"github.com/consensys/gnark-crypto/ecc/bw6-761/fp"
	"github.com/consensys/gnark-crypto/ecc/bw6-761/internal/fptower"
)

// GT target group of the pairing
type GT = fptower.E6

type lineEvaluation struct {
	r0 fp.Element
	r1 fp.Element
	r2 fp.Element
}

// Pair calculates the reduced pairing for a set of points
// ∏ᵢ e(Pᵢ, Qᵢ)
func Pair(P []G1Affine, Q []G2Affine) (GT, error) {
	f, err := MillerLoop(P, Q)
	if err != nil {
		return GT{}, err
	}
	return FinalExponentiation(&f), nil
}

// PairingCheck calculates the reduced pairing for a set of points and returns True if the result is One
// ∏ᵢ e(Pᵢ, Qᵢ) =? 1
func PairingCheck(P []G1Affine, Q []G2Affine) (bool, error) {
	f, err := Pair(P, Q)
	if err != nil {
		return false, err
	}
	var one GT
	one.SetOne()
	return f.Equal(&one), nil
}

// FinalExponentiation computes the exponentiation (∏ᵢ zᵢ)ᵈ
// where d = (p^6-1)/r = (p^6-1)/Φ_6(p) ⋅ Φ_6(p)/r = (p^3-1)(p+1)(p^2 - p +1)/r
// we use instead d=s ⋅ (p^3-1)(p+1)(p^2 - p +1)/r
// where s is the cofactor 12(x_0+1) (El Housni and Guillevic)
func FinalExponentiation(z *GT, _z ...*GT) GT {

	var result GT
	result.Set(z)

	for _, e := range _z {
		result.Mul(&result, e)
	}

	var buf GT

	// Easy part
	// (p^3-1)(p+1)
	buf.Conjugate(&result)
	result.Inverse(&result)
	buf.Mul(&buf, &result)
	result.Frobenius(&buf).
		Mul(&result, &buf)

		// Hard part (up to permutation)
		// El Housni and Guillevic
		// https://eprint.iacr.org/2020/351.pdf
	var f [8]GT
	var fp [10]GT
	f[0].Set(&result)
	fp[0].Frobenius(&result)
	for k := 1; k < 8; k++ {
		f[k].Expt(&f[k-1])
		fp[k].Frobenius(&f[k])
	}
	fp[8].Expt(&fp[7])
	fp[9].Expt(&fp[8])

	var tmp, f4fp2, f2fp4, f4fp2fp5, fp6fp8, f5fp7, f3f6, f1f7 GT
	result.Conjugate(&fp[5]).
		Mul(&result, &fp[6]).
		Mul(&result, &fp[3]).
		CyclotomicSquare(&result)
	f4fp2.Mul(&f[4], &fp[2])
	tmp.Mul(&f[0], &f[1]).
		Mul(&tmp, &f[3]).
		Mul(&tmp, &fp[8]).
		Mul(&tmp, &f4fp2).
		Conjugate(&tmp)
	result.Mul(&result, &f[5]).
		Mul(&result, &fp[0]).
		Mul(&result, &tmp).
		CyclotomicSquare(&result)
	tmp.Conjugate(&f[7]).
		Mul(&tmp, &fp[9])
	result.Mul(&result, &tmp).
		CyclotomicSquare(&result)
	f2fp4.Mul(&f[2], &fp[4])
	f4fp2fp5.Mul(&f4fp2, &fp[5])
	tmp.Mul(&f2fp4, &f[3]).
		Mul(&tmp, &fp[3]).
		Conjugate(&tmp)
	result.Mul(&result, &tmp).
		Mul(&result, &f[6]).
		Mul(&result, &fp[7]).
		Mul(&result, &f4fp2fp5).
		CyclotomicSquare(&result)
	tmp.Mul(&fp[0], &fp[9]).
		Conjugate(&tmp)
	result.Mul(&result, &tmp).
		Mul(&result, &f[0]).
		Mul(&result, &f[7]).
		Mul(&result, &fp[1]).
		CyclotomicSquare(&result)
	fp6fp8.Mul(&fp[6], &fp[8])
	f5fp7.Mul(&f[5], &fp[7])
	tmp.Conjugate(&fp6fp8)
	result.Mul(&result, &tmp).
		Mul(&result, &fp[2]).
		Mul(&result, &f5fp7).
		CyclotomicSquare(&result)
	f3f6.Mul(&f[3], &f[6])
	f1f7.Mul(&f[1], &f[7])
	tmp.Mul(&f1f7, &f[2]).
		Conjugate(&tmp)
	result.Mul(&result, &tmp).
		Mul(&result, &fp[9]).
		Mul(&result, &f3f6).
		CyclotomicSquare(&result)
	tmp.Mul(&f4fp2, &f5fp7).
		Mul(&tmp, &fp6fp8).
		Conjugate(&tmp)
	result.Mul(&result, &tmp).
		Mul(&result, &f[0]).
		Mul(&result, &fp[0]).
		Mul(&result, &fp[3]).
		Mul(&result, &fp[5]).
		CyclotomicSquare(&result)
	tmp.Conjugate(&f3f6).
		Mul(&tmp, &fp[1])
	result.Mul(&result, &tmp).
		CyclotomicSquare(&result)
	tmp.Mul(&f2fp4, &f4fp2fp5).
		Mul(&tmp, &fp[9]).
		Conjugate(&tmp)
	result.Mul(&result, &tmp).
		Mul(&result, &f1f7).
		Mul(&result, &f5fp7).
		Mul(&result, &fp[0])

	return result
}

// MillerLoop Optimal Tate alternative (or twisted ate or Eta revisited)
// computes the multi-Miller loop ∏ᵢ MillerLoop(Pᵢ, Qᵢ)
// Alg.2 in https://eprint.iacr.org/2021/1359.pdf
// Eq. (6) in https://hackmd.io/@gnark/BW6-761-changes
func MillerLoop(P []G1Affine, Q []G2Affine) (GT, error) {
	// check input size match
	n := len(P)
	if n == 0 || n != len(Q) {
		return GT{}, errors.New("invalid inputs sizes")
	}

	// filter infinity points
	p0 := make([]G1Affine, 0, n)
	q := make([]G2Affine, 0, n)

	for k := 0; k < n; k++ {
		if P[k].IsInfinity() || Q[k].IsInfinity() {
			continue
		}
		p0 = append(p0, P[k])
		q = append(q, Q[k])
	}

	n = len(q)

	// precomputations
	pProj1 := make([]g1Proj, n)
	p1 := make([]G1Affine, n)
	p01 := make([]G1Affine, n)
	p10 := make([]G1Affine, n)
	pProj01 := make([]g1Proj, n) // P0+P1
	pProj10 := make([]g1Proj, n) // P0-P1
	l01 := make([]lineEvaluation, n)
	l10 := make([]lineEvaluation, n)
	for k := 0; k < n; k++ {
		p1[k].Y.Neg(&p0[k].Y)
		p1[k].X.Mul(&p0[k].X, &thirdRootOneG2)
		pProj1[k].FromAffine(&p1[k])

		// l_{p0,p1}(q)
		pProj01[k].Set(&pProj1[k])
		pProj01[k].AddMixedStep(&l01[k], &p0[k])
		l01[k].r1.Mul(&l01[k].r1, &q[k].X)
		l01[k].r0.Mul(&l01[k].r0, &q[k].Y)

		// l_{p0,-p1}(q)
		pProj10[k].Neg(&pProj1[k])
		pProj10[k].AddMixedStep(&l10[k], &p0[k])
		l10[k].r1.Mul(&l10[k].r1, &q[k].X)
		l10[k].r0.Mul(&l10[k].r0, &q[k].Y)
	}
	BatchProjectiveToAffineG1(pProj01, p01)
	BatchProjectiveToAffineG1(pProj10, p10)

	// f_{a0+\lambda*a1,P}(Q)
	var result, ss GT
	result.SetOne()
	var l, l0 lineEvaluation

	var j int8

	// i = len(loopCounter) - 2
	for k := 0; k < n; k++ {
		pProj1[k].DoubleStep(&l0)
		l0.r1.Mul(&l0.r1, &q[k].X)
		l0.r0.Mul(&l0.r0, &q[k].Y)
		result.MulBy034(&l0.r0, &l0.r1, &l0.r2)
	}

	var tmp G1Affine
	for i := len(loopCounter0) - 3; i >= 0; i-- {
		// (∏ᵢfᵢ)²
		result.Square(&result)

		j = loopCounter1[i]*3 + loopCounter0[i]

		for k := 0; k < n; k++ {
			pProj1[k].DoubleStep(&l0)
			l0.r1.Mul(&l0.r1, &q[k].X)
			l0.r0.Mul(&l0.r0, &q[k].Y)

			switch j {
			case -4:
				tmp.Neg(&p01[k])
				pProj1[k].AddMixedStep(&l, &tmp)
				l.r1.Mul(&l.r1, &q[k].X)
				l.r0.Mul(&l.r0, &q[k].Y)
				ss.Mul034By034(&l.r0, &l.r1, &l.r2, &l01[k].r0, &l01[k].r1, &l01[k].r2)
				result.MulBy034(&l0.r0, &l0.r1, &l0.r2).
					Mul(&result, &ss)
			case -3:
				tmp.Neg(&p1[k])
				pProj1[k].AddMixedStep(&l, &tmp)
				l.r1.Mul(&l.r1, &q[k].X)
				l.r0.Mul(&l.r0, &q[k].Y)
				ss.Mul034By034(&l.r0, &l.r1, &l.r2, &l0.r0, &l0.r1, &l0.r2)
				result.Mul(&result, &ss)
			case -2:
				pProj1[k].AddMixedStep(&l, &p10[k])
				l.r1.Mul(&l.r1, &q[k].X)
				l.r0.Mul(&l.r0, &q[k].Y)
				ss.Mul034By034(&l.r0, &l.r1, &l.r2, &l01[k].r0, &l01[k].r1, &l01[k].r2)
				result.MulBy034(&l0.r0, &l0.r1, &l0.r2).
					Mul(&result, &ss)
			case -1:
				tmp.Neg(&p0[k])
				pProj1[k].AddMixedStep(&l, &tmp)
				l.r1.Mul(&l.r1, &q[k].X)
				l.r0.Mul(&l.r0, &q[k].Y)
				ss.Mul034By034(&l.r0, &l.r1, &l.r2, &l0.r0, &l0.r1, &l0.r2)
				result.Mul(&result, &ss)
			case 0:
				result.MulBy034(&l0.r0, &l0.r1, &l0.r2)
			case 1:
				pProj1[k].AddMixedStep(&l, &p0[k])
				l.r1.Mul(&l.r1, &q[k].X)
				l.r0.Mul(&l.r0, &q[k].Y)
				ss.Mul034By034(&l.r0, &l.r1, &l.r2, &l0.r0, &l0.r1, &l0.r2)
				result.Mul(&result, &ss)
			case 2:
				tmp.Neg(&p10[k])
				pProj1[k].AddMixedStep(&l, &tmp)
				l.r1.Mul(&l.r1, &q[k].X)
				l.r0.Mul(&l.r0, &q[k].Y)
				ss.Mul034By034(&l.r0, &l.r1, &l.r2, &l01[k].r0, &l01[k].r1, &l01[k].r2)
				result.MulBy034(&l0.r0, &l0.r1, &l0.r2).
					Mul(&result, &ss)
			case 3:
				pProj1[k].AddMixedStep(&l, &p1[k])
				l.r1.Mul(&l.r1, &q[k].X)
				l.r0.Mul(&l.r0, &q[k].Y)
				ss.Mul034By034(&l.r0, &l.r1, &l.r2, &l0.r0, &l0.r1, &l0.r2)
				result.Mul(&result, &ss)
			case 4:
				pProj1[k].AddMixedStep(&l, &p01[k])
				l.r1.Mul(&l.r1, &q[k].X)
				l.r0.Mul(&l.r0, &q[k].Y)
				ss.Mul034By034(&l.r0, &l.r1, &l.r2, &l01[k].r0, &l01[k].r1, &l01[k].r2)
				result.MulBy034(&l0.r0, &l0.r1, &l0.r2).
					Mul(&result, &ss)
			default:
				return GT{}, errors.New("invalid loopCounter")
			}
		}
	}

	return result, nil
}

// DoubleStep doubles a point in Homogenous projective coordinates, and evaluates the line in Miller loop
// https://eprint.iacr.org/2013/722.pdf (Section 4.3)
func (p *g1Proj) DoubleStep(evaluations *lineEvaluation) {

	// get some Element from our pool
	var t1, A, B, C, D, E, EE, F, G, H, I, J, K fp.Element
	A.Mul(&p.x, &p.y)
	A.Halve()
	B.Square(&p.y)
	C.Square(&p.z)
	D.Double(&C).
		Add(&D, &C)

		// E.Mul(&D, &bCurveCoeff)
	E.Neg(&D)

	F.Double(&E).
		Add(&F, &E)
	G.Add(&B, &F)
	G.Halve()
	H.Add(&p.y, &p.z).
		Square(&H)
	t1.Add(&B, &C)
	H.Sub(&H, &t1)
	I.Sub(&E, &B)
	J.Square(&p.x)
	EE.Square(&E)
	K.Double(&EE).
		Add(&K, &EE)

	// X, Y, Z
	p.x.Sub(&B, &F).
		Mul(&p.x, &A)
	p.y.Square(&G).
		Sub(&p.y, &K)
	p.z.Mul(&B, &H)

	// Line evaluation
	evaluations.r0.Neg(&H)
	evaluations.r1.Double(&J).
		Add(&evaluations.r1, &J)
	evaluations.r2.Set(&I)
}

// AddMixedStep point addition in Mixed Homogenous projective and Affine coordinates
// https://eprint.iacr.org/2013/722.pdf (Section 4.3)
func (p *g1Proj) AddMixedStep(evaluations *lineEvaluation, a *G1Affine) {

	// get some Element from our pool
	var Y2Z1, X2Z1, O, L, C, D, E, F, G, H, t0, t1, t2, J fp.Element
	Y2Z1.Mul(&a.Y, &p.z)
	O.Sub(&p.y, &Y2Z1)
	X2Z1.Mul(&a.X, &p.z)
	L.Sub(&p.x, &X2Z1)
	C.Square(&O)
	D.Square(&L)
	E.Mul(&L, &D)
	F.Mul(&p.z, &C)
	G.Mul(&p.x, &D)
	t0.Double(&G)
	H.Add(&E, &F).
		Sub(&H, &t0)
	t1.Mul(&p.y, &E)

	// X, Y, Z
	p.x.Mul(&L, &H)
	p.y.Sub(&G, &H).
		Mul(&p.y, &O).
		Sub(&p.y, &t1)
	p.z.Mul(&E, &p.z)

	t2.Mul(&L, &a.Y)
	J.Mul(&a.X, &O).
		Sub(&J, &t2)

	// Line evaluation
	evaluations.r0.Set(&L)
	evaluations.r1.Neg(&O)
	evaluations.r2.Set(&J)
}
