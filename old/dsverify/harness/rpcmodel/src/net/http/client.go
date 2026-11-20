package http

import (
	"bufio"
	"errors"
)

// Response is the part of Go's Response the model's callers use (SwiftPaxos's client reads the
// net/rpc server's answer to its CONNECT with ReadResponse): the status line's parts.
type Response struct {
	Status     string // "200 Connected to Go RPC": the status line after the protocol
	StatusCode int    // 200
	Proto      string // "HTTP/1.0"
}

var errStatus = errors.New("http: malformed HTTP response")

// readLine reads one line from r, without its "\n" or "\r\n".
func readLine(r *bufio.Reader) ([]byte, error) {
	line := make([]byte, 0, 64)
	for {
		if uint64(len(line)) >= maxHead {
			return nil, errHead
		}
		b, err := r.ReadByte()
		if err != nil {
			return nil, err
		}
		if b == '\n' {
			if len(line) > 0 && line[len(line)-1] == '\r' {
				return line[:len(line)-1], nil
			}
			return line, nil
		}
		line = append(line, b)
	}
}

// ReadResponse reads an HTTP response from r: its status line "PROTO CODE TEXT" and its header
// lines, up to the blank line (Go's ReadResponse, for a response without a body, as net/rpc's
// server's answer to CONNECT; the model keeps no headers and reads no body). The code is three
// digits; an error if the status line is malformed or a read fails. req is not used (Go's uses
// its method to decide whether a body follows: none follows a 2xx answer to CONNECT).
func ReadResponse(r *bufio.Reader, req *Request) (*Response, error) {
	line, err := readLine(r)
	if err != nil {
		return nil, err
	}
	sp := -1
	for i := 0; i < len(line); i++ {
		if line[i] == ' ' {
			sp = i
			break
		}
	}
	if sp <= 0 || len(line) < sp+4 {
		return nil, errStatus
	}
	code := 0
	for i := sp + 1; i < sp+4; i++ {
		if line[i] < '0' || line[i] > '9' {
			return nil, errStatus
		}
		code = code*10 + int(line[i]-'0')
	}
	if len(line) > sp+4 && line[sp+4] != ' ' {
		return nil, errStatus
	}
	resp := &Response{Status: string(line[sp+1:]), StatusCode: code, Proto: string(line[:sp])}
	for {
		h, err2 := readLine(r)
		if err2 != nil {
			return nil, err2
		}
		if len(h) == 0 {
			return resp, nil
		}
	}
}
