// Package status is the dsverify lab's model of google.golang.org/grpc/status (v1.84.0): a
// status is a code and a message; its error is a *statusError (the real one is
// *internal/status.Error, which no other package can name either).
//
// Deviations (notes/grpc-model.md): FromError, Code and Convert recognize the model's own status
// errors only, by their dynamic type; the real ones also accept any error type with a
// GRPCStatus() method and errors that wrap one (errors.As). No status details or proto form.
// Errorf and Newf format with fmt.Sprintf, as the real ones.
package status

import (
	"context"
	"fmt"

	"google.golang.org/grpc/codes"
)

// Status represents an RPC status code and message. A nil *Status is the status OK.
type Status struct {
	code codes.Code
	msg  string
}

// New returns a Status representing c and msg.
func New(c codes.Code, msg string) *Status {
	return &Status{code: c, msg: msg}
}

// Newf returns New(c, fmt.Sprintf(format, a...)).
func Newf(c codes.Code, format string, a ...interface{}) *Status {
	return New(c, fmt.Sprintf(format, a...))
}

// Error returns an error representing c and msg; nil if c is OK.
func Error(c codes.Code, msg string) error {
	return New(c, msg).Err()
}

// Errorf returns Error(c, fmt.Sprintf(format, a...)).
func Errorf(c codes.Code, format string, a ...interface{}) error {
	return Error(c, fmt.Sprintf(format, a...))
}

// Code returns the status code of s (OK for a nil s).
func (s *Status) Code() codes.Code {
	if s == nil {
		return codes.OK
	}
	return s.code
}

// Message returns the message of s ("" for a nil s).
func (s *Status) Message() string {
	if s == nil {
		return ""
	}
	return s.msg
}

// String is the real one's: "rpc error: code = <code> desc = <message>".
func (s *Status) String() string {
	return "rpc error: code = " + s.Code().String() + " desc = " + s.Message()
}

// Err returns an error representing s; nil if its code is OK.
func (s *Status) Err() error {
	if s.Code() == codes.OK {
		return nil
	}
	return &statusError{s: s}
}

// statusError is the error of a status (the real one's internal/status.Error).
type statusError struct {
	s *Status
}

// Error is the status's String().
func (e *statusError) Error() string {
	return e.s.String()
}

// GRPCStatus returns the error's status.
func (e *statusError) GRPCStatus() *Status {
	return e.s
}

// FromError returns err's status: (nil, true) for nil; err's own status and true for a status
// error; else a status Unknown with err's message, and false.
func FromError(err error) (*Status, bool) {
	if err == nil {
		return nil, true
	}
	if se, ok := err.(*statusError); ok {
		return se.s, true
	}
	return New(codes.Unknown, err.Error()), false
}

// Convert returns FromError's status.
func Convert(err error) *Status {
	s, _ := FromError(err)
	return s
}

// Code returns err's code: OK for nil, a status error's code, else Unknown.
func Code(err error) codes.Code {
	if err == nil {
		return codes.OK
	}
	if se, ok := err.(*statusError); ok {
		return se.s.Code()
	}
	return codes.Unknown
}

// FromContextError converts a context error into a status: nil for nil, DeadlineExceeded for
// context.DeadlineExceeded, Canceled for context.Canceled, else Unknown (with err's message).
func FromContextError(err error) *Status {
	if err == nil {
		return nil
	}
	if err == context.DeadlineExceeded {
		return New(codes.DeadlineExceeded, err.Error())
	}
	if err == context.Canceled {
		return New(codes.Canceled, err.Error())
	}
	return New(codes.Unknown, err.Error())
}
