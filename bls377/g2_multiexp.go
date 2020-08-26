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

// Code generated by gurvy DO NOT EDIT

package bls377

import "github.com/consensys/gurvy/bls377/fr"

// MultiExp implements section 4 of https://eprint.iacr.org/2012/549.pdf
// optionally, takes as parameter a MultiExpOptions struct
// enabling to set
// * the choice of  "c" (c-bit window to process the scalars)
// * max number of cpus to use
// * indicates wether or not the provided scalars are already partitionned using PartitionScalars method
func (p *G2Jac) MultiExp(points []G2Affine, scalars []fr.Element, opts ...MultiExpOptions) *G2Jac {
	// note:
	// each of the msmCX method is the same, except for the c constant it declares
	// duplicating (through template generation) these methods allows to declare the buckets on the stack
	// the choice of c needs to be improved:
	// there is a theoritical value that gives optimal asymptotics
	// but in practice, other factors come into play, including:
	// * if c doesn't divide 64, the word size, then we're bound to select bits over 2 words of our scalars, instead of 1
	// * number of CPUs
	// * cache friendliness (which depends on the host, G1 or G2... )
	//	--> for example, on BN256, a G1 point fits into one cache line of 64bytes, but a G2 point don't.

	// for each msmCX
	// step 1
	// we compute, for each scalars over c-bit wide windows, nbChunk digits
	// if the digit is larger than 2^{c-1}, then, we borrow 2^c from the next window and substract
	// 2^{c} to the current digit, making it negative.
	// negative digits will be processed in the next step as adding -G into the bucket instead of G
	// (computing -G is cheap, and this saves us half of the buckets)
	// step 2
	// buckets are declared on the stack
	// notice that we have 2^{c-1} buckets instead of 2^{c} (see step1)
	// we use jacobian extended formulas here as they are faster than mixed addition
	// msmProcessChunk places points into buckets base on their selector and return the weighted bucket sum in given channel
	// step 3
	// reduce the buckets weigthed sums into our result (msmReduceChunk)

	var opt MultiExpOptions
	if len(opts) > 0 {
		opt = opts[0]
	}
	opt.build(len(points))

	// semaphore to limit number of cpus iterating through points and scalrs at the same time
	chCpus := make(chan struct{}, opt.MaxCPUs)
	for i := 0; i < opt.MaxCPUs; i++ {
		chCpus <- struct{}{}
	}

	// partition the scalars
	// note: we do that before the actual chunk processing, as for each c-bit window (starting from LSW)
	// if it's larger than 2^{c-1}, we have a carry we need to propagate up to the higher window
	if !opt.IsPartitionned {
		scalars = PartitionScalars(scalars, opt)
	}

	switch opt.C {

	case 4:
		return p.msmC4(points, scalars, chCpus)

	case 5:
		return p.msmC5(points, scalars, chCpus)

	case 6:
		return p.msmC6(points, scalars, chCpus)

	case 7:
		return p.msmC7(points, scalars, chCpus)

	case 8:
		return p.msmC8(points, scalars, chCpus)

	case 9:
		return p.msmC9(points, scalars, chCpus)

	case 10:
		return p.msmC10(points, scalars, chCpus)

	case 11:
		return p.msmC11(points, scalars, chCpus)

	case 12:
		return p.msmC12(points, scalars, chCpus)

	case 13:
		return p.msmC13(points, scalars, chCpus)

	case 14:
		return p.msmC14(points, scalars, chCpus)

	case 15:
		return p.msmC15(points, scalars, chCpus)

	case 16:
		return p.msmC16(points, scalars, chCpus)

	case 17:
		return p.msmC17(points, scalars, chCpus)

	case 18:
		return p.msmC18(points, scalars, chCpus)

	case 19:
		return p.msmC19(points, scalars, chCpus)

	case 20:
		return p.msmC20(points, scalars, chCpus)

	default:
		panic("unimplemented")
	}
}

// msmReduceChunkG2 reduces the weighted sum of the buckets into the result of the multiExp
func msmReduceChunkG2(p *G2Jac, c int, chChunks []chan G2Jac) *G2Jac {
	totalj := <-chChunks[len(chChunks)-1]
	p.Set(&totalj)
	for j := len(chChunks) - 2; j >= 0; j-- {
		for l := 0; l < c; l++ {
			p.DoubleAssign()
		}
		totalj := <-chChunks[j]
		p.AddAssign(&totalj)
	}
	return p
}

func msmProcessChunkG2(chunk uint64,
	chRes chan<- G2Jac,
	chCpus chan struct{},
	buckets []g2JacExtended,
	c uint64,
	points []G2Affine,
	scalars []fr.Element) {

	<-chCpus // wait and decrement avaiable CPUs on the semaphore

	mask := uint64((1 << c) - 1) // low c bits are 1
	msbWindow := uint64(1 << (c - 1))

	for i := 0; i < len(buckets); i++ {
		buckets[i].SetInfinity()
	}

	jc := uint64(chunk * c)
	s := selector{}
	s.index = jc / 64
	s.shift = jc - (s.index * 64)
	s.mask = mask << s.shift
	s.multiWordSelect = (64%c) != 0 && s.shift > (64-c) && s.index < (fr.Limbs-1)
	if s.multiWordSelect {
		nbBitsHigh := s.shift - uint64(64-c)
		s.maskHigh = (1 << nbBitsHigh) - 1
		s.shiftHigh = (c - nbBitsHigh)
	}

	// for each scalars, get the digit corresponding to the chunk we're processing.
	for i := 0; i < len(scalars); i++ {
		bits := (scalars[i][s.index] & s.mask) >> s.shift
		if s.multiWordSelect {
			bits += (scalars[i][s.index+1] & s.maskHigh) << s.shiftHigh
		}

		if bits == 0 {
			continue
		}

		// if msbWindow bit is set, we need to substract
		if bits&msbWindow == 0 {
			// add
			buckets[bits-1].mAdd(&points[i])
		} else {
			// sub
			buckets[bits & ^msbWindow].mSub(&points[i])
		}
	}

	// reduce buckets into total
	// total =  bucket[0] + 2*bucket[1] + 3*bucket[2] ... + n*bucket[n-1]

	var runningSum, tj, total G2Jac
	runningSum.Set(&g2Infinity)
	total.Set(&g2Infinity)
	for k := len(buckets) - 1; k >= 0; k-- {
		if !buckets[k].ZZ.IsZero() {
			runningSum.AddAssign(tj.unsafeFromJacExtended(&buckets[k]))
		}
		total.AddAssign(&runningSum)
	}

	chRes <- total
	close(chRes)
	chCpus <- struct{}{} // increment avaiable CPUs into the semaphore
}

func (p *G2Jac) msmC4(points []G2Affine, scalars []fr.Element, chCpus chan struct{}) *G2Jac {
	const c = 4                          // scalars partitioned into c-bit radixes
	const nbChunks = (fr.Limbs * 64 / c) // number of c-bit radixes in a scalar

	// for each chunk, spawn a go routine that'll loop through all the scalars
	var chChunks [nbChunks]chan G2Jac
	for chunk := nbChunks - 1; chunk >= 0; chunk-- {
		chChunks[chunk] = make(chan G2Jac, 1)
		go func(j uint64) {
			var buckets [1 << (c - 1)]g2JacExtended
			msmProcessChunkG2(j, chChunks[j], chCpus, buckets[:], c, points, scalars)
		}(uint64(chunk))
	}

	return msmReduceChunkG2(p, c, chChunks[:])
}

func (p *G2Jac) msmC5(points []G2Affine, scalars []fr.Element, chCpus chan struct{}) *G2Jac {
	const c = 5                              // scalars partitioned into c-bit radixes
	const nbChunks = (fr.Limbs * 64 / c) + 1 // number of c-bit radixes in a scalar

	// for each chunk, spawn a go routine that'll loop through all the scalars
	var chChunks [nbChunks]chan G2Jac
	for chunk := nbChunks - 1; chunk >= 0; chunk-- {
		chChunks[chunk] = make(chan G2Jac, 1)
		go func(j uint64) {
			var buckets [1 << (c - 1)]g2JacExtended
			msmProcessChunkG2(j, chChunks[j], chCpus, buckets[:], c, points, scalars)
		}(uint64(chunk))
	}

	return msmReduceChunkG2(p, c, chChunks[:])
}

func (p *G2Jac) msmC6(points []G2Affine, scalars []fr.Element, chCpus chan struct{}) *G2Jac {
	const c = 6                              // scalars partitioned into c-bit radixes
	const nbChunks = (fr.Limbs * 64 / c) + 1 // number of c-bit radixes in a scalar

	// for each chunk, spawn a go routine that'll loop through all the scalars
	var chChunks [nbChunks]chan G2Jac
	for chunk := nbChunks - 1; chunk >= 0; chunk-- {
		chChunks[chunk] = make(chan G2Jac, 1)
		go func(j uint64) {
			var buckets [1 << (c - 1)]g2JacExtended
			msmProcessChunkG2(j, chChunks[j], chCpus, buckets[:], c, points, scalars)
		}(uint64(chunk))
	}

	return msmReduceChunkG2(p, c, chChunks[:])
}

func (p *G2Jac) msmC7(points []G2Affine, scalars []fr.Element, chCpus chan struct{}) *G2Jac {
	const c = 7                              // scalars partitioned into c-bit radixes
	const nbChunks = (fr.Limbs * 64 / c) + 1 // number of c-bit radixes in a scalar

	// for each chunk, spawn a go routine that'll loop through all the scalars
	var chChunks [nbChunks]chan G2Jac
	for chunk := nbChunks - 1; chunk >= 0; chunk-- {
		chChunks[chunk] = make(chan G2Jac, 1)
		go func(j uint64) {
			var buckets [1 << (c - 1)]g2JacExtended
			msmProcessChunkG2(j, chChunks[j], chCpus, buckets[:], c, points, scalars)
		}(uint64(chunk))
	}

	return msmReduceChunkG2(p, c, chChunks[:])
}

func (p *G2Jac) msmC8(points []G2Affine, scalars []fr.Element, chCpus chan struct{}) *G2Jac {
	const c = 8                          // scalars partitioned into c-bit radixes
	const nbChunks = (fr.Limbs * 64 / c) // number of c-bit radixes in a scalar

	// for each chunk, spawn a go routine that'll loop through all the scalars
	var chChunks [nbChunks]chan G2Jac
	for chunk := nbChunks - 1; chunk >= 0; chunk-- {
		chChunks[chunk] = make(chan G2Jac, 1)
		go func(j uint64) {
			var buckets [1 << (c - 1)]g2JacExtended
			msmProcessChunkG2(j, chChunks[j], chCpus, buckets[:], c, points, scalars)
		}(uint64(chunk))
	}

	return msmReduceChunkG2(p, c, chChunks[:])
}

func (p *G2Jac) msmC9(points []G2Affine, scalars []fr.Element, chCpus chan struct{}) *G2Jac {
	const c = 9                              // scalars partitioned into c-bit radixes
	const nbChunks = (fr.Limbs * 64 / c) + 1 // number of c-bit radixes in a scalar

	// for each chunk, spawn a go routine that'll loop through all the scalars
	var chChunks [nbChunks]chan G2Jac
	for chunk := nbChunks - 1; chunk >= 0; chunk-- {
		chChunks[chunk] = make(chan G2Jac, 1)
		go func(j uint64) {
			var buckets [1 << (c - 1)]g2JacExtended
			msmProcessChunkG2(j, chChunks[j], chCpus, buckets[:], c, points, scalars)
		}(uint64(chunk))
	}

	return msmReduceChunkG2(p, c, chChunks[:])
}

func (p *G2Jac) msmC10(points []G2Affine, scalars []fr.Element, chCpus chan struct{}) *G2Jac {
	const c = 10                             // scalars partitioned into c-bit radixes
	const nbChunks = (fr.Limbs * 64 / c) + 1 // number of c-bit radixes in a scalar

	// for each chunk, spawn a go routine that'll loop through all the scalars
	var chChunks [nbChunks]chan G2Jac
	for chunk := nbChunks - 1; chunk >= 0; chunk-- {
		chChunks[chunk] = make(chan G2Jac, 1)
		go func(j uint64) {
			var buckets [1 << (c - 1)]g2JacExtended
			msmProcessChunkG2(j, chChunks[j], chCpus, buckets[:], c, points, scalars)
		}(uint64(chunk))
	}

	return msmReduceChunkG2(p, c, chChunks[:])
}

func (p *G2Jac) msmC11(points []G2Affine, scalars []fr.Element, chCpus chan struct{}) *G2Jac {
	const c = 11                             // scalars partitioned into c-bit radixes
	const nbChunks = (fr.Limbs * 64 / c) + 1 // number of c-bit radixes in a scalar

	// for each chunk, spawn a go routine that'll loop through all the scalars
	var chChunks [nbChunks]chan G2Jac
	for chunk := nbChunks - 1; chunk >= 0; chunk-- {
		chChunks[chunk] = make(chan G2Jac, 1)
		go func(j uint64) {
			var buckets [1 << (c - 1)]g2JacExtended
			msmProcessChunkG2(j, chChunks[j], chCpus, buckets[:], c, points, scalars)
		}(uint64(chunk))
	}

	return msmReduceChunkG2(p, c, chChunks[:])
}

func (p *G2Jac) msmC12(points []G2Affine, scalars []fr.Element, chCpus chan struct{}) *G2Jac {
	const c = 12                             // scalars partitioned into c-bit radixes
	const nbChunks = (fr.Limbs * 64 / c) + 1 // number of c-bit radixes in a scalar

	// for each chunk, spawn a go routine that'll loop through all the scalars
	var chChunks [nbChunks]chan G2Jac
	for chunk := nbChunks - 1; chunk >= 0; chunk-- {
		chChunks[chunk] = make(chan G2Jac, 1)
		go func(j uint64) {
			var buckets [1 << (c - 1)]g2JacExtended
			msmProcessChunkG2(j, chChunks[j], chCpus, buckets[:], c, points, scalars)
		}(uint64(chunk))
	}

	return msmReduceChunkG2(p, c, chChunks[:])
}

func (p *G2Jac) msmC13(points []G2Affine, scalars []fr.Element, chCpus chan struct{}) *G2Jac {
	const c = 13                             // scalars partitioned into c-bit radixes
	const nbChunks = (fr.Limbs * 64 / c) + 1 // number of c-bit radixes in a scalar

	// for each chunk, spawn a go routine that'll loop through all the scalars
	var chChunks [nbChunks]chan G2Jac
	for chunk := nbChunks - 1; chunk >= 0; chunk-- {
		chChunks[chunk] = make(chan G2Jac, 1)
		go func(j uint64) {
			var buckets [1 << (c - 1)]g2JacExtended
			msmProcessChunkG2(j, chChunks[j], chCpus, buckets[:], c, points, scalars)
		}(uint64(chunk))
	}

	return msmReduceChunkG2(p, c, chChunks[:])
}

func (p *G2Jac) msmC14(points []G2Affine, scalars []fr.Element, chCpus chan struct{}) *G2Jac {
	const c = 14                             // scalars partitioned into c-bit radixes
	const nbChunks = (fr.Limbs * 64 / c) + 1 // number of c-bit radixes in a scalar

	// for each chunk, spawn a go routine that'll loop through all the scalars
	var chChunks [nbChunks]chan G2Jac
	for chunk := nbChunks - 1; chunk >= 0; chunk-- {
		chChunks[chunk] = make(chan G2Jac, 1)
		go func(j uint64) {
			var buckets [1 << (c - 1)]g2JacExtended
			msmProcessChunkG2(j, chChunks[j], chCpus, buckets[:], c, points, scalars)
		}(uint64(chunk))
	}

	return msmReduceChunkG2(p, c, chChunks[:])
}

func (p *G2Jac) msmC15(points []G2Affine, scalars []fr.Element, chCpus chan struct{}) *G2Jac {
	const c = 15                             // scalars partitioned into c-bit radixes
	const nbChunks = (fr.Limbs * 64 / c) + 1 // number of c-bit radixes in a scalar

	// for each chunk, spawn a go routine that'll loop through all the scalars
	var chChunks [nbChunks]chan G2Jac
	for chunk := nbChunks - 1; chunk >= 0; chunk-- {
		chChunks[chunk] = make(chan G2Jac, 1)
		go func(j uint64) {
			var buckets [1 << (c - 1)]g2JacExtended
			msmProcessChunkG2(j, chChunks[j], chCpus, buckets[:], c, points, scalars)
		}(uint64(chunk))
	}

	return msmReduceChunkG2(p, c, chChunks[:])
}

func (p *G2Jac) msmC16(points []G2Affine, scalars []fr.Element, chCpus chan struct{}) *G2Jac {
	const c = 16                         // scalars partitioned into c-bit radixes
	const nbChunks = (fr.Limbs * 64 / c) // number of c-bit radixes in a scalar

	// for each chunk, spawn a go routine that'll loop through all the scalars
	var chChunks [nbChunks]chan G2Jac
	for chunk := nbChunks - 1; chunk >= 0; chunk-- {
		chChunks[chunk] = make(chan G2Jac, 1)
		go func(j uint64) {
			var buckets [1 << (c - 1)]g2JacExtended
			msmProcessChunkG2(j, chChunks[j], chCpus, buckets[:], c, points, scalars)
		}(uint64(chunk))
	}

	return msmReduceChunkG2(p, c, chChunks[:])
}

func (p *G2Jac) msmC17(points []G2Affine, scalars []fr.Element, chCpus chan struct{}) *G2Jac {
	const c = 17                             // scalars partitioned into c-bit radixes
	const nbChunks = (fr.Limbs * 64 / c) + 1 // number of c-bit radixes in a scalar

	// for each chunk, spawn a go routine that'll loop through all the scalars
	var chChunks [nbChunks]chan G2Jac
	for chunk := nbChunks - 1; chunk >= 0; chunk-- {
		chChunks[chunk] = make(chan G2Jac, 1)
		go func(j uint64) {
			var buckets [1 << (c - 1)]g2JacExtended
			msmProcessChunkG2(j, chChunks[j], chCpus, buckets[:], c, points, scalars)
		}(uint64(chunk))
	}

	return msmReduceChunkG2(p, c, chChunks[:])
}

func (p *G2Jac) msmC18(points []G2Affine, scalars []fr.Element, chCpus chan struct{}) *G2Jac {
	const c = 18                             // scalars partitioned into c-bit radixes
	const nbChunks = (fr.Limbs * 64 / c) + 1 // number of c-bit radixes in a scalar

	// for each chunk, spawn a go routine that'll loop through all the scalars
	var chChunks [nbChunks]chan G2Jac
	for chunk := nbChunks - 1; chunk >= 0; chunk-- {
		chChunks[chunk] = make(chan G2Jac, 1)
		go func(j uint64) {
			var buckets [1 << (c - 1)]g2JacExtended
			msmProcessChunkG2(j, chChunks[j], chCpus, buckets[:], c, points, scalars)
		}(uint64(chunk))
	}

	return msmReduceChunkG2(p, c, chChunks[:])
}

func (p *G2Jac) msmC19(points []G2Affine, scalars []fr.Element, chCpus chan struct{}) *G2Jac {
	const c = 19                             // scalars partitioned into c-bit radixes
	const nbChunks = (fr.Limbs * 64 / c) + 1 // number of c-bit radixes in a scalar

	// for each chunk, spawn a go routine that'll loop through all the scalars
	var chChunks [nbChunks]chan G2Jac
	for chunk := nbChunks - 1; chunk >= 0; chunk-- {
		chChunks[chunk] = make(chan G2Jac, 1)
		go func(j uint64) {
			var buckets [1 << (c - 1)]g2JacExtended
			msmProcessChunkG2(j, chChunks[j], chCpus, buckets[:], c, points, scalars)
		}(uint64(chunk))
	}

	return msmReduceChunkG2(p, c, chChunks[:])
}

func (p *G2Jac) msmC20(points []G2Affine, scalars []fr.Element, chCpus chan struct{}) *G2Jac {
	const c = 20                             // scalars partitioned into c-bit radixes
	const nbChunks = (fr.Limbs * 64 / c) + 1 // number of c-bit radixes in a scalar

	// for each chunk, spawn a go routine that'll loop through all the scalars
	var chChunks [nbChunks]chan G2Jac
	for chunk := nbChunks - 1; chunk >= 0; chunk-- {
		chChunks[chunk] = make(chan G2Jac, 1)
		go func(j uint64) {
			var buckets [1 << (c - 1)]g2JacExtended
			msmProcessChunkG2(j, chChunks[j], chCpus, buckets[:], c, points, scalars)
		}(uint64(chunk))
	}

	return msmReduceChunkG2(p, c, chChunks[:])
}
