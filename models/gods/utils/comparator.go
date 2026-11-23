// Copyright (c) 2015, Emir Pasic. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package utils

// MODEL: only the Comparator type, which treemap.NewWith takes. gods' predefined comparators
// (StringComparator, IntComparator, ..., TimeComparator) are left out: no program here calls them
// (models/README.md, "The third-party library models").

// Comparator will make type assertion (see IntComparator for example),
// which will panic if a or b are not of the asserted type.
//
// Should return a number:
//    negative , if a < b
//    zero     , if a == b
//    positive , if a > b
type Comparator func(a, b interface{}) int
