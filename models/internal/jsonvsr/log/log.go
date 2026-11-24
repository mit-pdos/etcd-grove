// Copied from go-vsr (github.com/tangledbytes/go-vsr, Apache License 2.0), the dsverify
// verification fork as the dsv-vr kit has it (examples/dsverify/vr/pkg/log/log.go, 9cbb866 of the
// fork): as it is, with Logs' own MarshalJSON and UnmarshalJSON.
// A test input of the encoding/json model: what the vsr-net kit sends over TCP as JSON
// (../json.toml; the stream tests in ../../jsonstreamtest).

package log

import "encoding/json"

type Log struct {
	Data      string `json:"data"`
	ClientID  uint64 `json:"client_id,string"`
	RequestID uint64 `json:"request_id,string"`
}

type Logs []Log

func NewLogs() Logs {
	return make(Logs, 0)
}

func (l Logs) Len() int {
	return len(l)
}

func (l *Logs) Add(log Log) {
	*l = append(*l, log)
}

func (l Logs) OpAt(i int) string {
	return (l)[i-1].Data
}

func (l Logs) ClientIDAt(i int) uint64 {
	return (l)[i-1].ClientID
}

func (l Logs) RequestIDAt(i int) uint64 {
	return (l)[i-1].RequestID
}

// TruncateAfter keeps ops 1..i (OpAt(i) is the i-th entry) and drops the ops after i.
func (l *Logs) TruncateAfter(i int) {
	*l = (*l)[:i]
}

func (l *Logs) After(i int) Logs {
	return (*l)[i:]
}

func (l *Logs) Merge(logs Logs) {
	*l = append(*l, logs...)
}

func (l Logs) Last() Log {
	return l[len(l)-1]
}

func (l *Logs) UnmarshalJSON(data []byte) error {
	var logs []Log
	if err := json.Unmarshal(data, &logs); err != nil {
		return err
	}

	*l = logs
	return nil
}

func (l Logs) MarshalJSON() ([]byte, error) {
	return json.Marshal([]Log(l))
}
