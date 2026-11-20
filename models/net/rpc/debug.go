// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package rpc

/*
	Some HTML presented at http://machine:port/debug/rpc
	Lists services, their methods, and some statistics, still rudimentary.
*/

// MODEL: the debugging page (an html/template over reflection's method types) is not
// modelled: HandleHTTP registers its handler at debugPath as Go's does (so a second
// registration on the path panics in the mux, as Go's), and serving a request there panics.

import (
	"net/http"
)

// If set, print log statements for internal and I/O errors.
var debugLog = false

type debugHTTP struct {
	*Server
}

// Runs at /debug/rpc
func (server debugHTTP) ServeHTTP(w http.ResponseWriter, req *http.Request) {
	panic(notModelled("net/rpc model: the debugging page is not modelled"))
}
