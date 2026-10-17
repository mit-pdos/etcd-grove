// Copyright 2026 The etcd Authors
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

package ioutil

import (
	"io"
	"testing"
)

// dataEOFReader returns all its data in one Read together with io.EOF, as io.Reader allows
// ("a Reader returning a non-zero number of bytes at the end of the input stream may return
// either err == EOF or err == nil").
type dataEOFReader struct{ data []byte }

func (r *dataEOFReader) Read(p []byte) (int, error) {
	if len(r.data) == 0 {
		return 0, io.EOF
	}
	n := copy(p, r.data)
	r.data = r.data[n:]
	if len(r.data) == 0 {
		return n, io.EOF
	}
	return n, nil
}

func (r *dataEOFReader) Close() error { return nil }

// TestExactReadCloserShortWithDataEOF: a reader that ends short of the expected size with
// (n > 0, io.EOF) is read to the end with no error: the exact reader passes the io.EOF through.
// Only Close reports ErrShortRead.
func TestExactReadCloserShortWithDataEOF(t *testing.T) {
	rc := NewExactReadCloser(&dataEOFReader{data: []byte("hello")}, 10)
	b, err := io.ReadAll(rc)
	if err == nil {
		t.Errorf("read %d of 10 bytes with no error (%q)", len(b), b)
	}
	if cerr := rc.Close(); cerr != ErrShortRead {
		t.Errorf("Close() = %v, want ErrShortRead", cerr)
	}
}
