// Copyright 2010 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// MODEL: the build constraint goexperiment.jsonv2 is dropped (the model is this build's,
// the default one; the v1 implementation's files, decode.go, encode.go, ..., are not part
// of the model).

package json

// Valid reports whether data is a valid JSON encoding.
//
// MODEL: the program's codec's scanner decides (model.go).
func Valid(data []byte) bool {
	return valid(getCodec(), data)
}

// A SyntaxError is a description of a JSON syntax error.
// [Unmarshal] will return a SyntaxError if the JSON can't be parsed.
type SyntaxError struct {
	msg    string // description of error
	Offset int64  // error occurred after reading Offset bytes
}

func (e *SyntaxError) Error() string { return e.msg }

// MODEL: the translation of encoding/json/jsontext's syntax errors is not part of the model
// (its errors are the codec's: model.go).
