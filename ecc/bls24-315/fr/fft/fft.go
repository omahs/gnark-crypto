// Copyright 2020 ConsenSys Software Inc.
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

// Code generated by consensys/gnark-crypto DO NOT EDIT

package fft

import (
	"math/bits"
	"runtime"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/internal/parallel"

	"github.com/consensys/gnark-crypto/ecc/bls24-315/fr"
)

// Decimation is used in the FFT call to select decimation in time or in frequency
type Decimation uint8

const (
	DIT Decimation = iota
	DIF
	SPLITDIF
)

// parallelize threshold for a single butterfly op, if the fft stage is not parallelized already
const butterflyThreshold = 16

// FFT computes (recursively) the discrete Fourier transform of a and stores the result in a
// if decimation == DIT (decimation in time), the input must be in bit-reversed order
// if decimation == DIF (decimation in frequency), the output will be in bit-reversed order
// coset sets the shift of the fft (0 = no shift, standard fft)
// len(a) must be a power of 2, and w must be a len(a)th root of unity in field F.
//
// example:
// -------
// domain := NewDomain(m, 2) -->  contains precomputed data for Z/mZ, and Z/4mZ
// FFT(pol, DIT, 1) --> evaluates pol on the coset 1 in (Z/4mZ)/(Z/mZ)
func (domain *Domain) FFT(a []fr.Element, decimation Decimation, coset uint64) {

	numCPU := uint64(runtime.NumCPU())

	// if coset != 0, scale by coset table
	if coset != 0 {
		scale := func(cosetTable []fr.Element) {
			parallel.Execute(len(a), func(start, end int) {
				for i := start; i < end; i++ {
					a[i].Mul(&a[i], &cosetTable[i])
				}
			})
		}
		if decimation == DIT {
			if domain.PrecomputeReversedTable == 0 {
				// no precomputed coset, we adjust the index of the coset table
				n := uint64(len(a))
				nn := uint64(64 - bits.TrailingZeros64(n))
				parallel.Execute(len(a), func(start, end int) {
					for i := start; i < end; i++ {
						irev := bits.Reverse64(uint64(i)) >> nn
						a[i].Mul(&a[i], &domain.CosetTable[coset-1][int(irev)])
					}
				})
			} else {
				scale(domain.CosetTableReversed[coset-1])
			}
		} else {
			scale(domain.CosetTable[coset-1])
		}
	}

	// find the stage where we should stop spawning go routines in our recursive calls
	// (ie when we have as many go routines running as we have available CPUs)
	maxSplits := bits.TrailingZeros64(ecc.NextPowerOfTwo(numCPU))
	if numCPU <= 1 {
		maxSplits = -1
	}

	switch decimation {
	case DIF:
		difFFT(a, domain.Twiddles, 0, maxSplits, nil)
	case SPLITDIF:
		domain.difFFTSplit(a)
	case DIT:
		ditFFT(a, domain.Twiddles, 0, maxSplits, nil)
	default:
		panic("not implemented")
	}
}

// FFTInverse computes (recursively) the inverse discrete Fourier transform of a and stores the result in a
// if decimation == DIT (decimation in time), the input must be in bit-reversed order
// if decimation == DIF (decimation in frequency), the output will be in bit-reversed order
// coset sets the shift of the fft (0 = no shift, standard fft)
// len(a) must be a power of 2, and w must be a len(a)th root of unity in field F.
func (domain *Domain) FFTInverse(a []fr.Element, decimation Decimation, coset uint64) {

	numCPU := uint64(runtime.NumCPU())

	// find the stage where we should stop spawning go routines in our recursive calls
	// (ie when we have as many go routines running as we have available CPUs)
	maxSplits := bits.TrailingZeros64(ecc.NextPowerOfTwo(numCPU))
	if numCPU <= 1 {
		maxSplits = -1
	}
	switch decimation {
	case DIF:
		difFFT(a, domain.TwiddlesInv, 0, maxSplits, nil)
	case DIT:
		ditFFT(a, domain.TwiddlesInv, 0, maxSplits, nil)
	default:
		panic("not implemented")
	}

	// scale by CardinalityInv (+ cosetTableInv is coset!=0)
	if coset == 0 {
		parallel.Execute(len(a), func(start, end int) {
			for i := start; i < end; i++ {
				a[i].Mul(&a[i], &domain.CardinalityInv)
			}
		})
		return
	}

	scale := func(cosetTable []fr.Element) {
		parallel.Execute(len(a), func(start, end int) {
			for i := start; i < end; i++ {
				a[i].Mul(&a[i], &cosetTable[i]).
					Mul(&a[i], &domain.CardinalityInv)
			}
		})
	}
	if decimation == DIT {
		scale(domain.CosetTableInv[coset-1])
		return
	}

	// decimation == DIF
	if domain.PrecomputeReversedTable != 0 {
		scale(domain.CosetTableInvReversed[coset-1])
		return
	}

	// no precomputed coset, we adjust the index of the coset table
	n := uint64(len(a))
	nn := uint64(64 - bits.TrailingZeros64(n))
	parallel.Execute(len(a), func(start, end int) {
		for i := start; i < end; i++ {
			irev := bits.Reverse64(uint64(i)) >> nn
			a[i].Mul(&a[i], &domain.CosetTableInv[coset-1][int(irev)]).
				Mul(&a[i], &domain.CardinalityInv)
		}
	})

}

func kerDIF32(a []fr.Element, twiddles [][]fr.Element, stage int) {

	fr.Butterfly(&a[0], &a[16])
	fr.Butterfly(&a[1], &a[17])
	a[17].Mul(&a[17], &twiddles[stage+0][1])
	fr.Butterfly(&a[2], &a[18])
	a[18].Mul(&a[18], &twiddles[stage+0][2])
	fr.Butterfly(&a[3], &a[19])
	a[19].Mul(&a[19], &twiddles[stage+0][3])
	fr.Butterfly(&a[4], &a[20])
	a[20].Mul(&a[20], &twiddles[stage+0][4])
	fr.Butterfly(&a[5], &a[21])
	a[21].Mul(&a[21], &twiddles[stage+0][5])
	fr.Butterfly(&a[6], &a[22])
	a[22].Mul(&a[22], &twiddles[stage+0][6])
	fr.Butterfly(&a[7], &a[23])
	a[23].Mul(&a[23], &twiddles[stage+0][7])
	fr.Butterfly(&a[8], &a[24])
	a[24].Mul(&a[24], &twiddles[stage+0][8])
	fr.Butterfly(&a[9], &a[25])
	a[25].Mul(&a[25], &twiddles[stage+0][9])
	fr.Butterfly(&a[10], &a[26])
	a[26].Mul(&a[26], &twiddles[stage+0][10])
	fr.Butterfly(&a[11], &a[27])
	a[27].Mul(&a[27], &twiddles[stage+0][11])
	fr.Butterfly(&a[12], &a[28])
	a[28].Mul(&a[28], &twiddles[stage+0][12])
	fr.Butterfly(&a[13], &a[29])
	a[29].Mul(&a[29], &twiddles[stage+0][13])
	fr.Butterfly(&a[14], &a[30])
	a[30].Mul(&a[30], &twiddles[stage+0][14])
	fr.Butterfly(&a[15], &a[31])
	a[31].Mul(&a[31], &twiddles[stage+0][15])

	fr.Butterfly(&a[0], &a[8])
	fr.Butterfly(&a[1], &a[9])
	a[9].Mul(&a[9], &twiddles[stage+1][1])
	fr.Butterfly(&a[2], &a[10])
	a[10].Mul(&a[10], &twiddles[stage+1][2])
	fr.Butterfly(&a[3], &a[11])
	a[11].Mul(&a[11], &twiddles[stage+1][3])
	fr.Butterfly(&a[4], &a[12])
	a[12].Mul(&a[12], &twiddles[stage+1][4])
	fr.Butterfly(&a[5], &a[13])
	a[13].Mul(&a[13], &twiddles[stage+1][5])
	fr.Butterfly(&a[6], &a[14])
	a[14].Mul(&a[14], &twiddles[stage+1][6])
	fr.Butterfly(&a[7], &a[15])
	a[15].Mul(&a[15], &twiddles[stage+1][7])
	fr.Butterfly(&a[16], &a[24])
	fr.Butterfly(&a[17], &a[25])
	a[25].Mul(&a[25], &twiddles[stage+1][1])
	fr.Butterfly(&a[18], &a[26])
	a[26].Mul(&a[26], &twiddles[stage+1][2])
	fr.Butterfly(&a[19], &a[27])
	a[27].Mul(&a[27], &twiddles[stage+1][3])
	fr.Butterfly(&a[20], &a[28])
	a[28].Mul(&a[28], &twiddles[stage+1][4])
	fr.Butterfly(&a[21], &a[29])
	a[29].Mul(&a[29], &twiddles[stage+1][5])
	fr.Butterfly(&a[22], &a[30])
	a[30].Mul(&a[30], &twiddles[stage+1][6])
	fr.Butterfly(&a[23], &a[31])
	a[31].Mul(&a[31], &twiddles[stage+1][7])

	fr.Butterfly(&a[0], &a[4])
	fr.Butterfly(&a[1], &a[5])
	a[5].Mul(&a[5], &twiddles[stage+2][1])
	fr.Butterfly(&a[2], &a[6])
	a[6].Mul(&a[6], &twiddles[stage+2][2])
	fr.Butterfly(&a[3], &a[7])
	a[7].Mul(&a[7], &twiddles[stage+2][3])
	fr.Butterfly(&a[8], &a[12])
	fr.Butterfly(&a[9], &a[13])
	a[13].Mul(&a[13], &twiddles[stage+2][1])
	fr.Butterfly(&a[10], &a[14])
	a[14].Mul(&a[14], &twiddles[stage+2][2])
	fr.Butterfly(&a[11], &a[15])
	a[15].Mul(&a[15], &twiddles[stage+2][3])
	fr.Butterfly(&a[16], &a[20])
	fr.Butterfly(&a[17], &a[21])
	a[21].Mul(&a[21], &twiddles[stage+2][1])
	fr.Butterfly(&a[18], &a[22])
	a[22].Mul(&a[22], &twiddles[stage+2][2])
	fr.Butterfly(&a[19], &a[23])
	a[23].Mul(&a[23], &twiddles[stage+2][3])
	fr.Butterfly(&a[24], &a[28])
	fr.Butterfly(&a[25], &a[29])
	a[29].Mul(&a[29], &twiddles[stage+2][1])
	fr.Butterfly(&a[26], &a[30])
	a[30].Mul(&a[30], &twiddles[stage+2][2])
	fr.Butterfly(&a[27], &a[31])
	a[31].Mul(&a[31], &twiddles[stage+2][3])

	fr.Butterfly(&a[0], &a[2])
	fr.Butterfly(&a[1], &a[3])
	a[3].Mul(&a[3], &twiddles[stage+3][1])
	fr.Butterfly(&a[4], &a[6])
	fr.Butterfly(&a[5], &a[7])
	a[7].Mul(&a[7], &twiddles[stage+3][1])
	fr.Butterfly(&a[8], &a[10])
	fr.Butterfly(&a[9], &a[11])
	a[11].Mul(&a[11], &twiddles[stage+3][1])
	fr.Butterfly(&a[12], &a[14])
	fr.Butterfly(&a[13], &a[15])
	a[15].Mul(&a[15], &twiddles[stage+3][1])
	fr.Butterfly(&a[16], &a[18])
	fr.Butterfly(&a[17], &a[19])
	a[19].Mul(&a[19], &twiddles[stage+3][1])
	fr.Butterfly(&a[20], &a[22])
	fr.Butterfly(&a[21], &a[23])
	a[23].Mul(&a[23], &twiddles[stage+3][1])
	fr.Butterfly(&a[24], &a[26])
	fr.Butterfly(&a[25], &a[27])
	a[27].Mul(&a[27], &twiddles[stage+3][1])
	fr.Butterfly(&a[28], &a[30])
	fr.Butterfly(&a[29], &a[31])
	a[31].Mul(&a[31], &twiddles[stage+3][1])

	fr.Butterfly(&a[0], &a[1])
	fr.Butterfly(&a[2], &a[3])
	fr.Butterfly(&a[4], &a[5])
	fr.Butterfly(&a[6], &a[7])
	fr.Butterfly(&a[8], &a[9])
	fr.Butterfly(&a[10], &a[11])
	fr.Butterfly(&a[12], &a[13])
	fr.Butterfly(&a[14], &a[15])
	fr.Butterfly(&a[16], &a[17])
	fr.Butterfly(&a[18], &a[19])
	fr.Butterfly(&a[20], &a[21])
	fr.Butterfly(&a[22], &a[23])
	fr.Butterfly(&a[24], &a[25])
	fr.Butterfly(&a[26], &a[27])
	fr.Butterfly(&a[28], &a[29])
	fr.Butterfly(&a[30], &a[31])

}

func difFFT(a []fr.Element, twiddles [][]fr.Element, stage, maxSplits int, chDone chan struct{}) {
	if chDone != nil {
		defer func() {
			close(chDone)
		}()
	}
	n := len(a)
	if n == 1 {
		return
	} else if n == 32 {
		kerDIF32(a, twiddles, stage)
		return
	}
	m := n >> 1

	// if stage < maxSplits, we parallelize this butterfly
	// but we have only numCPU / stage cpus available
	if (m > butterflyThreshold) && (stage < maxSplits) {
		// 1 << stage == estimated used CPUs
		numCPU := runtime.NumCPU() / (1 << (stage))
		parallel.Execute(m, func(start, end int) {
			for i := start; i < end; i++ {
				fr.Butterfly(&a[i], &a[i+m])
				a[i+m].Mul(&a[i+m], &twiddles[stage][i])
			}
		}, numCPU)
	} else {

		// i == 0
		fr.Butterfly(&a[0], &a[m])
		for i := 1; i < m; i++ {
			fr.Butterfly(&a[i], &a[i+m])
			a[i+m].Mul(&a[i+m], &twiddles[stage][i])
		}
	}

	if m == 1 {
		return
	}

	nextStage := stage + 1
	if stage < maxSplits {
		chDone := make(chan struct{}, 1)
		go difFFT(a[m:n], twiddles, nextStage, maxSplits, chDone)
		difFFT(a[0:m], twiddles, nextStage, maxSplits, nil)
		<-chDone
	} else {
		difFFT(a[0:m], twiddles, nextStage, maxSplits, nil)
		difFFT(a[m:n], twiddles, nextStage, maxSplits, nil)
	}
}

func ditFFT(a []fr.Element, twiddles [][]fr.Element, stage, maxSplits int, chDone chan struct{}) {
	if chDone != nil {
		defer func() {
			close(chDone)
		}()
	}
	n := len(a)
	if n == 1 {
		return
	}
	m := n >> 1

	nextStage := stage + 1

	if stage < maxSplits {
		// that's the only time we fire go routines
		chDone := make(chan struct{}, 1)
		go ditFFT(a[m:], twiddles, nextStage, maxSplits, chDone)
		ditFFT(a[0:m], twiddles, nextStage, maxSplits, nil)
		<-chDone
	} else {
		ditFFT(a[0:m], twiddles, nextStage, maxSplits, nil)
		ditFFT(a[m:n], twiddles, nextStage, maxSplits, nil)

	}

	// if stage < maxSplits, we parallelize this butterfly
	// but we have only numCPU / stage cpus available
	if (m > butterflyThreshold) && (stage < maxSplits) {
		// 1 << stage == estimated used CPUs
		numCPU := runtime.NumCPU() / (1 << (stage))
		parallel.Execute(m, func(start, end int) {
			for k := start; k < end; k++ {
				a[k+m].Mul(&a[k+m], &twiddles[stage][k])
				fr.Butterfly(&a[k], &a[k+m])
			}
		}, numCPU)

	} else {
		fr.Butterfly(&a[0], &a[m])
		for k := 1; k < m; k++ {
			a[k+m].Mul(&a[k+m], &twiddles[stage][k])
			fr.Butterfly(&a[k], &a[k+m])
		}
	}
}

// BitReverse applies the bit-reversal permutation to a.
// len(a) must be a power of 2 (as in every single function in this file)
func BitReverse(a []fr.Element) {
	n := uint64(len(a))
	nn := uint64(64 - bits.TrailingZeros64(n))

	for i := uint64(0); i < n; i++ {
		irev := bits.Reverse64(i) >> nn
		if irev > i {
			a[i], a[irev] = a[irev], a[i]
		}
	}
}

// TODO add sources. Mostly from OpenZKP and Winterfell
// Square transpose from https://faculty.kfupm.edu.sa/COE/mayez/xeon-phi/Xeon-Phi-Mat-Transpose/Transposition%20of%20Square-Xeon-Phi.pdf

func (domain *Domain) difFFTSplit(a []fr.Element) {
	n := len(a)

	innerLen := 1 << (bits.TrailingZeros64(uint64(n)) / 2)
	outerLen := n / innerLen

	ratio := outerLen / innerLen
	// if ratio == 1 	--> square matrix innerLen * innerLen
	// if ratio == 2 	--> rect matrix innerLen * innerLen * 2

	twiddles := domain.SplitTwiddles[0]

	// transpose inner x inner x stretch square matrix
	transposeMatrix(a, innerLen, ratio)

	nbRows := n / outerLen

	// apply inner FFTs on each row
	parallel.Execute(nbRows, func(start, end int) {
		for i := start; i < end; i++ {
			s := i * outerLen
			ss := s + outerLen
			innerSplitFFT1(a[s:ss], twiddles, 0, ratio == 2)
		}
	})

	// transpose inner x inner x stretch square matrix
	transposeMatrix(a, innerLen, ratio)

	nn := uint64(64 - bits.TrailingZeros64(uint64(innerLen)))

	parallel.Execute(nbRows, func(startRow, endRow int) {
		for ; startRow < endRow; startRow++ {
			i := startRow * outerLen
			if i != 0 {
				irev := bits.Reverse64(uint64(startRow)) >> nn
				for j := 1; j < outerLen; j++ {
					a[i+j].Mul(&a[i+j], &domain.SplitTwiddles[irev+1][j-1])
				}
			}
			innerSplitFFT1(a[i:i+outerLen], twiddles, 0, false)
		}
	})

}

func transposeMatrix(matrix []fr.Element, size int, ratio int) {
	if ratio == 1 {
		transposeSquare(matrix, size)
	} else if ratio == 2 {
		transposeRect(matrix, size)
	} else {
		panic("not implemented")
	}
}

func transposeSquareOld(matrix []fr.Element, size int) {
	// matrix.len() == size * size
	// iterate over upper-left triangle, working in 2x2 blocks
	for row := 0; row < size; row += 2 {
		i := row*size + row
		matrix[i+1], matrix[i+size] = matrix[i+size], matrix[i+1]

		for col := row + 2; col < size; col += 2 {
			i := row*size + col
			j := col*size + row
			matrix[i], matrix[j] = matrix[j], matrix[i]
			matrix[i+1], matrix[j+size] = matrix[j+size], matrix[i+1]
			matrix[i+size], matrix[j+1] = matrix[j+1], matrix[i+size]
			matrix[i+size+1], matrix[j+size+1] = matrix[j+size+1], matrix[i+size+1]
		}
	}
}

const TILE = 16 // 16 ?

func nestedLoopPlan(n int) (plan []int) {
	nEven := n - n%TILE
	wTiles := nEven / TILE
	i := 0
	plan = make([]int, wTiles*(wTiles-1)) // TODO fix size

	for j := 1; j < wTiles; j++ {
		for k := 0; k < j; k++ {
			plan[2*i] = j * TILE
			plan[2*i+1] = k * TILE
			i++
		}
	}
	return
}

func transposeSquare(a []fr.Element, size int) {
	nEven := size - size%TILE
	wTiles := nEven / TILE
	nTilesParallel := wTiles * (wTiles - 1) / 2
	plan := nestedLoopPlan(size)

	parallel.Execute(nTilesParallel, func(start, end int) {
		for k := start; k < end; k++ {
			ii := plan[2*k]
			jj := plan[2*k+1]
			for j := jj; j < jj+TILE; j++ {
				for i := ii; i < ii+TILE; i++ {
					a[i*size+j], a[j*size+i] = a[j*size+i], a[i*size+j]
				}
			}
		}
	})

	for ii := 0; ii < nEven; ii += TILE {
		for j := ii; j < ii+TILE; j++ {
			for i := ii; i < j; i++ {
				a[i*size+j], a[j*size+i] = a[j*size+i], a[i*size+j]
			}
		}
	}
	for j := 0; j < nEven; j++ {
		for i := nEven; i < size; i++ {
			a[i*size+j], a[j*size+i] = a[j*size+i], a[i*size+j]
		}
	}

	for j := nEven; j < size; j++ {
		for i := nEven; i < j; i++ {
			a[i*size+j], a[j*size+i] = a[j*size+i], a[i*size+j]
		}
	}

}

func transposeRect(matrix []fr.Element, size int) {
	// matrix.len() == size * size * 2
	// iterate over upper-left triangle, working in 1x2 blocks
	for row := 0; row < size; row++ {
		for col := row + 1; col < size; col++ {
			i := (row*size + col) * 2
			j := (col*size + row) * 2
			matrix[i], matrix[j] = matrix[j], matrix[i]
			matrix[i+1], matrix[j+1] = matrix[j+1], matrix[i+1]
		}
	}
}

func innerSplitFFT1(a []fr.Element, twiddles []fr.Element, tIndex int, skipLast bool) {
	n := len(a)
	if n == 1 || (skipLast && n == 2) {
		return
	} else if n == 32 && !skipLast {
		if tIndex == 0 {
			kerDIFSplit16Zero(a, twiddles)
		} else {
			kerDIFSplit16(a, twiddles, tIndex)
		}
		return
	}
	m := n >> 1

	if tIndex == 0 {
		for i := 0; i < m; i++ {
			fr.Butterfly(&a[i], &a[i+m])
		}
	} else {
		for i := 0; i < m; i++ {
			a[i+m].Mul(&a[i+m], &twiddles[tIndex])
			fr.Butterfly(&a[i], &a[i+m])
		}
	}
	tIndex <<= 1
	if m == 1 || (skipLast && m == 2) {
		return
	}
	innerSplitFFT1(a[:m], twiddles, tIndex, skipLast)
	innerSplitFFT1(a[m:], twiddles, tIndex+1, skipLast)

}

func kerDIFSplit16(a []fr.Element, twiddles []fr.Element, tIndex int) {

	a[16].Mul(&a[16], &twiddles[tIndex+0])
	fr.Butterfly(&a[0], &a[16])
	a[17].Mul(&a[17], &twiddles[tIndex+0])
	fr.Butterfly(&a[1], &a[17])
	a[18].Mul(&a[18], &twiddles[tIndex+0])
	fr.Butterfly(&a[2], &a[18])
	a[19].Mul(&a[19], &twiddles[tIndex+0])
	fr.Butterfly(&a[3], &a[19])
	a[20].Mul(&a[20], &twiddles[tIndex+0])
	fr.Butterfly(&a[4], &a[20])
	a[21].Mul(&a[21], &twiddles[tIndex+0])
	fr.Butterfly(&a[5], &a[21])
	a[22].Mul(&a[22], &twiddles[tIndex+0])
	fr.Butterfly(&a[6], &a[22])
	a[23].Mul(&a[23], &twiddles[tIndex+0])
	fr.Butterfly(&a[7], &a[23])
	a[24].Mul(&a[24], &twiddles[tIndex+0])
	fr.Butterfly(&a[8], &a[24])
	a[25].Mul(&a[25], &twiddles[tIndex+0])
	fr.Butterfly(&a[9], &a[25])
	a[26].Mul(&a[26], &twiddles[tIndex+0])
	fr.Butterfly(&a[10], &a[26])
	a[27].Mul(&a[27], &twiddles[tIndex+0])
	fr.Butterfly(&a[11], &a[27])
	a[28].Mul(&a[28], &twiddles[tIndex+0])
	fr.Butterfly(&a[12], &a[28])
	a[29].Mul(&a[29], &twiddles[tIndex+0])
	fr.Butterfly(&a[13], &a[29])
	a[30].Mul(&a[30], &twiddles[tIndex+0])
	fr.Butterfly(&a[14], &a[30])
	a[31].Mul(&a[31], &twiddles[tIndex+0])
	fr.Butterfly(&a[15], &a[31])
	tIndex <<= 1

	a[8].Mul(&a[8], &twiddles[tIndex+0])
	fr.Butterfly(&a[0], &a[8])
	a[9].Mul(&a[9], &twiddles[tIndex+0])
	fr.Butterfly(&a[1], &a[9])
	a[10].Mul(&a[10], &twiddles[tIndex+0])
	fr.Butterfly(&a[2], &a[10])
	a[11].Mul(&a[11], &twiddles[tIndex+0])
	fr.Butterfly(&a[3], &a[11])
	a[12].Mul(&a[12], &twiddles[tIndex+0])
	fr.Butterfly(&a[4], &a[12])
	a[13].Mul(&a[13], &twiddles[tIndex+0])
	fr.Butterfly(&a[5], &a[13])
	a[14].Mul(&a[14], &twiddles[tIndex+0])
	fr.Butterfly(&a[6], &a[14])
	a[15].Mul(&a[15], &twiddles[tIndex+0])
	fr.Butterfly(&a[7], &a[15])
	a[24].Mul(&a[24], &twiddles[tIndex+1])
	fr.Butterfly(&a[16], &a[24])
	a[25].Mul(&a[25], &twiddles[tIndex+1])
	fr.Butterfly(&a[17], &a[25])
	a[26].Mul(&a[26], &twiddles[tIndex+1])
	fr.Butterfly(&a[18], &a[26])
	a[27].Mul(&a[27], &twiddles[tIndex+1])
	fr.Butterfly(&a[19], &a[27])
	a[28].Mul(&a[28], &twiddles[tIndex+1])
	fr.Butterfly(&a[20], &a[28])
	a[29].Mul(&a[29], &twiddles[tIndex+1])
	fr.Butterfly(&a[21], &a[29])
	a[30].Mul(&a[30], &twiddles[tIndex+1])
	fr.Butterfly(&a[22], &a[30])
	a[31].Mul(&a[31], &twiddles[tIndex+1])
	fr.Butterfly(&a[23], &a[31])
	tIndex <<= 1

	a[4].Mul(&a[4], &twiddles[tIndex+0])
	fr.Butterfly(&a[0], &a[4])
	a[5].Mul(&a[5], &twiddles[tIndex+0])
	fr.Butterfly(&a[1], &a[5])
	a[6].Mul(&a[6], &twiddles[tIndex+0])
	fr.Butterfly(&a[2], &a[6])
	a[7].Mul(&a[7], &twiddles[tIndex+0])
	fr.Butterfly(&a[3], &a[7])
	a[12].Mul(&a[12], &twiddles[tIndex+1])
	fr.Butterfly(&a[8], &a[12])
	a[13].Mul(&a[13], &twiddles[tIndex+1])
	fr.Butterfly(&a[9], &a[13])
	a[14].Mul(&a[14], &twiddles[tIndex+1])
	fr.Butterfly(&a[10], &a[14])
	a[15].Mul(&a[15], &twiddles[tIndex+1])
	fr.Butterfly(&a[11], &a[15])
	a[20].Mul(&a[20], &twiddles[tIndex+2])
	fr.Butterfly(&a[16], &a[20])
	a[21].Mul(&a[21], &twiddles[tIndex+2])
	fr.Butterfly(&a[17], &a[21])
	a[22].Mul(&a[22], &twiddles[tIndex+2])
	fr.Butterfly(&a[18], &a[22])
	a[23].Mul(&a[23], &twiddles[tIndex+2])
	fr.Butterfly(&a[19], &a[23])
	a[28].Mul(&a[28], &twiddles[tIndex+3])
	fr.Butterfly(&a[24], &a[28])
	a[29].Mul(&a[29], &twiddles[tIndex+3])
	fr.Butterfly(&a[25], &a[29])
	a[30].Mul(&a[30], &twiddles[tIndex+3])
	fr.Butterfly(&a[26], &a[30])
	a[31].Mul(&a[31], &twiddles[tIndex+3])
	fr.Butterfly(&a[27], &a[31])
	tIndex <<= 1

	a[2].Mul(&a[2], &twiddles[tIndex+0])
	fr.Butterfly(&a[0], &a[2])
	a[3].Mul(&a[3], &twiddles[tIndex+0])
	fr.Butterfly(&a[1], &a[3])
	a[6].Mul(&a[6], &twiddles[tIndex+1])
	fr.Butterfly(&a[4], &a[6])
	a[7].Mul(&a[7], &twiddles[tIndex+1])
	fr.Butterfly(&a[5], &a[7])
	a[10].Mul(&a[10], &twiddles[tIndex+2])
	fr.Butterfly(&a[8], &a[10])
	a[11].Mul(&a[11], &twiddles[tIndex+2])
	fr.Butterfly(&a[9], &a[11])
	a[14].Mul(&a[14], &twiddles[tIndex+3])
	fr.Butterfly(&a[12], &a[14])
	a[15].Mul(&a[15], &twiddles[tIndex+3])
	fr.Butterfly(&a[13], &a[15])
	a[18].Mul(&a[18], &twiddles[tIndex+4])
	fr.Butterfly(&a[16], &a[18])
	a[19].Mul(&a[19], &twiddles[tIndex+4])
	fr.Butterfly(&a[17], &a[19])
	a[22].Mul(&a[22], &twiddles[tIndex+5])
	fr.Butterfly(&a[20], &a[22])
	a[23].Mul(&a[23], &twiddles[tIndex+5])
	fr.Butterfly(&a[21], &a[23])
	a[26].Mul(&a[26], &twiddles[tIndex+6])
	fr.Butterfly(&a[24], &a[26])
	a[27].Mul(&a[27], &twiddles[tIndex+6])
	fr.Butterfly(&a[25], &a[27])
	a[30].Mul(&a[30], &twiddles[tIndex+7])
	fr.Butterfly(&a[28], &a[30])
	a[31].Mul(&a[31], &twiddles[tIndex+7])
	fr.Butterfly(&a[29], &a[31])
	tIndex <<= 1

	a[1].Mul(&a[1], &twiddles[tIndex+0])
	fr.Butterfly(&a[0], &a[1])
	a[3].Mul(&a[3], &twiddles[tIndex+1])
	fr.Butterfly(&a[2], &a[3])
	a[5].Mul(&a[5], &twiddles[tIndex+2])
	fr.Butterfly(&a[4], &a[5])
	a[7].Mul(&a[7], &twiddles[tIndex+3])
	fr.Butterfly(&a[6], &a[7])
	a[9].Mul(&a[9], &twiddles[tIndex+4])
	fr.Butterfly(&a[8], &a[9])
	a[11].Mul(&a[11], &twiddles[tIndex+5])
	fr.Butterfly(&a[10], &a[11])
	a[13].Mul(&a[13], &twiddles[tIndex+6])
	fr.Butterfly(&a[12], &a[13])
	a[15].Mul(&a[15], &twiddles[tIndex+7])
	fr.Butterfly(&a[14], &a[15])
	a[17].Mul(&a[17], &twiddles[tIndex+8])
	fr.Butterfly(&a[16], &a[17])
	a[19].Mul(&a[19], &twiddles[tIndex+9])
	fr.Butterfly(&a[18], &a[19])
	a[21].Mul(&a[21], &twiddles[tIndex+10])
	fr.Butterfly(&a[20], &a[21])
	a[23].Mul(&a[23], &twiddles[tIndex+11])
	fr.Butterfly(&a[22], &a[23])
	a[25].Mul(&a[25], &twiddles[tIndex+12])
	fr.Butterfly(&a[24], &a[25])
	a[27].Mul(&a[27], &twiddles[tIndex+13])
	fr.Butterfly(&a[26], &a[27])
	a[29].Mul(&a[29], &twiddles[tIndex+14])
	fr.Butterfly(&a[28], &a[29])
	a[31].Mul(&a[31], &twiddles[tIndex+15])
	fr.Butterfly(&a[30], &a[31])
	tIndex <<= 1

}

func kerDIFSplit16Zero(a []fr.Element, twiddles []fr.Element) {

	fr.Butterfly(&a[0], &a[16])
	fr.Butterfly(&a[1], &a[17])
	fr.Butterfly(&a[2], &a[18])
	fr.Butterfly(&a[3], &a[19])
	fr.Butterfly(&a[4], &a[20])
	fr.Butterfly(&a[5], &a[21])
	fr.Butterfly(&a[6], &a[22])
	fr.Butterfly(&a[7], &a[23])
	fr.Butterfly(&a[8], &a[24])
	fr.Butterfly(&a[9], &a[25])
	fr.Butterfly(&a[10], &a[26])
	fr.Butterfly(&a[11], &a[27])
	fr.Butterfly(&a[12], &a[28])
	fr.Butterfly(&a[13], &a[29])
	fr.Butterfly(&a[14], &a[30])
	fr.Butterfly(&a[15], &a[31])

	fr.Butterfly(&a[0], &a[8])
	fr.Butterfly(&a[1], &a[9])
	fr.Butterfly(&a[2], &a[10])
	fr.Butterfly(&a[3], &a[11])
	fr.Butterfly(&a[4], &a[12])
	fr.Butterfly(&a[5], &a[13])
	fr.Butterfly(&a[6], &a[14])
	fr.Butterfly(&a[7], &a[15])
	a[24].Mul(&a[24], &twiddles[1])
	fr.Butterfly(&a[16], &a[24])
	a[25].Mul(&a[25], &twiddles[1])
	fr.Butterfly(&a[17], &a[25])
	a[26].Mul(&a[26], &twiddles[1])
	fr.Butterfly(&a[18], &a[26])
	a[27].Mul(&a[27], &twiddles[1])
	fr.Butterfly(&a[19], &a[27])
	a[28].Mul(&a[28], &twiddles[1])
	fr.Butterfly(&a[20], &a[28])
	a[29].Mul(&a[29], &twiddles[1])
	fr.Butterfly(&a[21], &a[29])
	a[30].Mul(&a[30], &twiddles[1])
	fr.Butterfly(&a[22], &a[30])
	a[31].Mul(&a[31], &twiddles[1])
	fr.Butterfly(&a[23], &a[31])

	fr.Butterfly(&a[0], &a[4])
	fr.Butterfly(&a[1], &a[5])
	fr.Butterfly(&a[2], &a[6])
	fr.Butterfly(&a[3], &a[7])
	a[12].Mul(&a[12], &twiddles[1])
	fr.Butterfly(&a[8], &a[12])
	a[13].Mul(&a[13], &twiddles[1])
	fr.Butterfly(&a[9], &a[13])
	a[14].Mul(&a[14], &twiddles[1])
	fr.Butterfly(&a[10], &a[14])
	a[15].Mul(&a[15], &twiddles[1])
	fr.Butterfly(&a[11], &a[15])
	a[20].Mul(&a[20], &twiddles[2])
	fr.Butterfly(&a[16], &a[20])
	a[21].Mul(&a[21], &twiddles[2])
	fr.Butterfly(&a[17], &a[21])
	a[22].Mul(&a[22], &twiddles[2])
	fr.Butterfly(&a[18], &a[22])
	a[23].Mul(&a[23], &twiddles[2])
	fr.Butterfly(&a[19], &a[23])
	a[28].Mul(&a[28], &twiddles[3])
	fr.Butterfly(&a[24], &a[28])
	a[29].Mul(&a[29], &twiddles[3])
	fr.Butterfly(&a[25], &a[29])
	a[30].Mul(&a[30], &twiddles[3])
	fr.Butterfly(&a[26], &a[30])
	a[31].Mul(&a[31], &twiddles[3])
	fr.Butterfly(&a[27], &a[31])

	fr.Butterfly(&a[0], &a[2])
	fr.Butterfly(&a[1], &a[3])
	a[6].Mul(&a[6], &twiddles[1])
	fr.Butterfly(&a[4], &a[6])
	a[7].Mul(&a[7], &twiddles[1])
	fr.Butterfly(&a[5], &a[7])
	a[10].Mul(&a[10], &twiddles[2])
	fr.Butterfly(&a[8], &a[10])
	a[11].Mul(&a[11], &twiddles[2])
	fr.Butterfly(&a[9], &a[11])
	a[14].Mul(&a[14], &twiddles[3])
	fr.Butterfly(&a[12], &a[14])
	a[15].Mul(&a[15], &twiddles[3])
	fr.Butterfly(&a[13], &a[15])
	a[18].Mul(&a[18], &twiddles[4])
	fr.Butterfly(&a[16], &a[18])
	a[19].Mul(&a[19], &twiddles[4])
	fr.Butterfly(&a[17], &a[19])
	a[22].Mul(&a[22], &twiddles[5])
	fr.Butterfly(&a[20], &a[22])
	a[23].Mul(&a[23], &twiddles[5])
	fr.Butterfly(&a[21], &a[23])
	a[26].Mul(&a[26], &twiddles[6])
	fr.Butterfly(&a[24], &a[26])
	a[27].Mul(&a[27], &twiddles[6])
	fr.Butterfly(&a[25], &a[27])
	a[30].Mul(&a[30], &twiddles[7])
	fr.Butterfly(&a[28], &a[30])
	a[31].Mul(&a[31], &twiddles[7])
	fr.Butterfly(&a[29], &a[31])

	fr.Butterfly(&a[0], &a[1])
	a[3].Mul(&a[3], &twiddles[1])
	fr.Butterfly(&a[2], &a[3])
	a[5].Mul(&a[5], &twiddles[2])
	fr.Butterfly(&a[4], &a[5])
	a[7].Mul(&a[7], &twiddles[3])
	fr.Butterfly(&a[6], &a[7])
	a[9].Mul(&a[9], &twiddles[4])
	fr.Butterfly(&a[8], &a[9])
	a[11].Mul(&a[11], &twiddles[5])
	fr.Butterfly(&a[10], &a[11])
	a[13].Mul(&a[13], &twiddles[6])
	fr.Butterfly(&a[12], &a[13])
	a[15].Mul(&a[15], &twiddles[7])
	fr.Butterfly(&a[14], &a[15])
	a[17].Mul(&a[17], &twiddles[8])
	fr.Butterfly(&a[16], &a[17])
	a[19].Mul(&a[19], &twiddles[9])
	fr.Butterfly(&a[18], &a[19])
	a[21].Mul(&a[21], &twiddles[10])
	fr.Butterfly(&a[20], &a[21])
	a[23].Mul(&a[23], &twiddles[11])
	fr.Butterfly(&a[22], &a[23])
	a[25].Mul(&a[25], &twiddles[12])
	fr.Butterfly(&a[24], &a[25])
	a[27].Mul(&a[27], &twiddles[13])
	fr.Butterfly(&a[26], &a[27])
	a[29].Mul(&a[29], &twiddles[14])
	fr.Butterfly(&a[28], &a[29])
	a[31].Mul(&a[31], &twiddles[15])
	fr.Butterfly(&a[30], &a[31])

}
