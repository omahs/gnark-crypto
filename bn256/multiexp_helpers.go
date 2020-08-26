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

package bn256

import (
	"math"
	"runtime"

	"github.com/consensys/gurvy/bn256/fr"
	"github.com/consensys/gurvy/utils/parallel"
)

// MultiExpOptions enables users to set optional parameters to the multiexp
type MultiExpOptions struct {
	IsPartitionned bool   // indicates whether or not the scalars inputs are already partitionned
	C              uint64 // sets the "c" parameter (window size)
	MaxCPUs        int    // sets max CPUs to use. ignored if <0 or > runtime.NumCPUs()
}

func (opt *MultiExpOptions) build(nbPoints int) {
	// implemented msmC methods (the c we use must be in this slice)
	implementedCs := []uint64{4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20}

	if opt.C != 0 {
		// C is set, ensure the implementation exists.
		found := false
		for i := 0; i < len(implementedCs); i++ {
			if implementedCs[i] == opt.C {
				found = true
				break
			}
		}
		if !found {
			panic("invalid option: unsupported C value")
		}
	} else {
		// C is not set, use default value
		// approximate cost (in group operations)
		// cost = bits/c * (nbPoints + 2^{c-1})
		// this needs to be verified empirically.
		// for example, on a MBP 2016, for G2 MultiExp > 8M points, hand picking c gives better results
		min := math.MaxFloat64
		for _, c := range implementedCs {
			cc := fr.Limbs * 64 * (nbPoints + (1 << (c - 1)))
			cost := float64(cc) / float64(c)
			if cost < min {
				min = cost
				opt.C = c
			}
		}
	}

	// available cpus
	numCpus := runtime.NumCPU()
	if !(opt.MaxCPUs > 0 && opt.MaxCPUs < numCpus) {
		opt.MaxCPUs = numCpus
	}

}

// selector stores the index, mask and shifts needed to select bits from a scalar
// it is used during the multiExp algorithm or the batch scalar multiplication
type selector struct {
	index uint64 // index in the multi-word scalar to select bits from
	mask  uint64 // mask (c-bit wide)
	shift uint64 // shift needed to get our bits on low positions

	multiWordSelect bool   // set to true if we need to select bits from 2 words (case where c doesn't divide 64)
	maskHigh        uint64 // same than mask, for index+1
	shiftHigh       uint64 // same than shift, for index+1
}

// PartitionScalars  compute, for each scalars over c-bit wide windows, nbChunk digits
// if the digit is larger than 2^{c-1}, then, we borrow 2^c from the next window and substract
// 2^{c} to the current digit, making it negative.
// negative digits can be processed in a later step as adding -G into the bucket instead of G
// (computing -G is cheap, and this saves us half of the buckets in the MultiExp or BatchScalarMul)
func PartitionScalars(scalars []fr.Element, opts ...MultiExpOptions) []fr.Element {
	toReturn := make([]fr.Element, len(scalars))

	var opt MultiExpOptions
	if len(opts) > 0 {
		opt = opts[0]
	}
	opt.build(len(scalars))
	c := opt.C

	// number of c-bit radixes in a scalar
	nbChunks := fr.Limbs * 64 / c
	if (fr.Limbs*64)%c != 0 {
		nbChunks++
	}

	mask := uint64((1 << c) - 1)      // low c bits are 1
	msbWindow := uint64(1 << (c - 1)) // msb of the c-bit window
	max := int(1 << (c - 1))          // max value we want for our digits
	cDivides64 := (64 % c) == 0       // if c doesn't divide 64, we may need to select over multiple words

	// compute offset and word selector / shift to select the right bits of our windows
	selectors := make([]selector, nbChunks)
	for chunk := uint64(0); chunk < nbChunks; chunk++ {
		jc := uint64(chunk * c)
		d := selector{}
		d.index = jc / 64
		d.shift = jc - (d.index * 64)
		d.mask = mask << d.shift
		d.multiWordSelect = !cDivides64 && d.shift > (64-c) && d.index < (fr.Limbs-1)
		if d.multiWordSelect {
			nbBitsHigh := d.shift - uint64(64-c)
			d.maskHigh = (1 << nbBitsHigh) - 1
			d.shiftHigh = (c - nbBitsHigh)
		}
		selectors[chunk] = d
	}

	parallel.Execute(len(scalars), func(start, end int) {
		for i := start; i < end; i++ {
			var carry int

			// for each chunk in the scalar, compute the current digit, and an eventual carry
			for chunk := uint64(0); chunk < nbChunks; chunk++ {
				s := selectors[chunk]

				// init with carry if any
				digit := carry
				carry = 0

				// digit = value of the c-bit window
				digit += int((scalars[i][s.index] & s.mask) >> s.shift)

				if s.multiWordSelect {
					// we are selecting bits over 2 words
					digit += int(scalars[i][s.index+1]&s.maskHigh) << s.shiftHigh
				}

				// if the digit is larger than 2^{c-1}, then, we borrow 2^c from the next window and substract
				// 2^{c} to the current digit, making it negative.
				if digit >= max {
					digit -= (1 << c)
					carry = 1
				}

				var bits uint64
				if digit >= 0 {
					bits = uint64(digit)
				} else {
					bits = uint64(-digit-1) | msbWindow
				}

				toReturn[i][s.index] |= (bits << s.shift)
				if s.multiWordSelect {
					toReturn[i][s.index+1] |= (bits >> s.shiftHigh)
				}

			}
		}
	}, opt.MaxCPUs)
	return toReturn
}
