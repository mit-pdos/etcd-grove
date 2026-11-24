package httpdifftest

import (
	"io"
	"log"
)

// quietLog is a server's ErrorLog that discards (both builds log the same errors).
func quietLog() *log.Logger { return log.New(io.Discard, "", 0) }
