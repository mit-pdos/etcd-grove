/*
 *
 * Copyright 2026 the etcd-grove authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 */

package grpc

// MODEL: the model's choice points. These two functions are the model's only nondeterminism, and
// the only declarations of the package with a hand-written GooseLang body (trusted: any boolean,
// any index below n; so the model has every behavior on either side of a choice). In Go they
// take the common side (false, 0), so that a real run behaves as grpc-go usually does, unless the
// environment variable GRPC_MODEL_CHOOSE is "random" when the program starts: then each choice is
// random (a test knob, to run the model's rare paths: refused streams, idleness, failures of a
// fail-fast pick, the code of a transport failure, which reported address is dialed).

import (
	"math/rand/v2"
	"os"
)

var modelChooseRandom = os.Getenv("GRPC_MODEL_CHOOSE") == "random"

// modelChoose is an arbitrary boolean.
func modelChoose() bool {
	if modelChooseRandom {
		return rand.IntN(2) == 0
	}
	return false
}

// modelChooseN is an arbitrary index below n (n > 0).
func modelChooseN(n int) int {
	if modelChooseRandom && n > 0 {
		return rand.IntN(n)
	}
	return 0
}
