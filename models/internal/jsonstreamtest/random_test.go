package jsonstreamtest

import (
	"crypto/sha256"
	"encoding/json"
	"fmt"
	"io"
	"math/rand"
	"os"
	"strconv"
	"strings"
	"testing"

	"models.lab/internal/jsonvsr/events"
)

// TestRandomStreams: random streams (vsr events as wire.Encode writes them, numbers, literals,
// strings, arrays and objects, whitespace, stray delimiters and bytes, deep nesting, values longer
// than the buffer; cut at a random point) read in random chunk sizes, ending with io.EOF or a read
// error, decoded by one Decoder into random targets (a frame, a uint64, a RawMessage, an event's
// message); one line per stream in the transcript: the last decode and the SHA-256 of the whole
// (every Read with its length, every Decode's result, InputOffset, Buffered). The streams have no
// escape sequence or non-ASCII byte in a string the codec decodes (the model panics there).
// JSONSTREAM_RANDOM: the number of streams (default 3000; the golden transcript is of the default;
// for another number, JSONSTREAM_OUT=FILE writes the transcript, to compare the two builds' by hand).
func TestRandomStreams(t *testing.T) {
	n := 3000
	if s, err := strconv.Atoi(os.Getenv("JSONSTREAM_RANDOM")); err == nil && s > 0 {
		n = s
	}
	r := rand.New(rand.NewSource(7))
	evs := encodeAll(sampleEvents(), &strings.Builder{})
	var events1 [][]byte
	for _, l := range strings.SplitAfter(string(evs), "\n") {
		if l != "" {
			events1 = append(events1, []byte(l))
		}
	}
	var tr strings.Builder
	for i := 0; i < n; i++ {
		var sb strings.Builder
		for k := r.Intn(6); k >= 0; k-- {
			sb.WriteString(randomPiece(r, events1))
		}
		stream := []byte(sb.String())
		if r.Intn(3) == 0 {
			stream = stream[:r.Intn(len(stream)+1)]
		}
		var sizes []int
		for k := 1 + r.Intn(4); k > 0; k-- {
			sizes = append(sizes, []int{1, 2, 3, 5, 8, 13, 63, 64, 65, 100, 1000, 5000}[r.Intn(12)])
		}
		end := io.EOF
		if r.Intn(4) == 0 {
			end = errBoom
		}
		var sc strings.Builder
		fmt.Fprintf(&sc, "stream %d: %d bytes, chunks %v, end %s\n", i, len(stream), sizes, errClass(end))
		dec := json.NewDecoder(&script{data: stream, sizes: sizes, end: end, log: &sc})
		for j := 0; j < 12; j++ {
			var err error
			var got string
			switch r.Intn(4) {
			case 0:
				var frame struct {
					Type events.EventType `json:"@type"`
					Data json.RawMessage  `json:"data"`
				}
				err = dec.Decode(&frame)
				got = fmt.Sprintf("frame %d %d", frame.Type, len(frame.Data))
			case 1:
				var x uint64
				err = dec.Decode(&x)
				got = fmt.Sprintf("uint64 %d", x)
			case 2:
				var raw json.RawMessage
				err = dec.Decode(&raw)
				got = fmt.Sprintf("raw %d", len(raw))
			default:
				var x events.Prepare
				err = dec.Decode(&x)
				got = fmt.Sprintf("prepare %d %d %q", x.ViewNum, x.OpNum, x.Request.Op)
			}
			rest, _ := io.ReadAll(dec.Buffered())
			fmt.Fprintf(&sc, " decode %d: %s %s offset %d buffered %d\n", j, errClass(err), got, dec.InputOffset(), len(rest))
			if c := errClass(err); c == "EOF" || c == "UnexpectedEOF" || c == "boom" {
				break
			}
		}
		// one line per stream: its number, the last decode, the SHA-256 (first 16 hex digits)
		lines := strings.Split(strings.TrimSuffix(sc.String(), "\n"), "\n")
		sum := sha256.Sum256([]byte(sc.String()))
		fmt.Fprintf(&tr, "%d:%s %x\n", i, lines[len(lines)-1], sum[:8])
	}
	if out := os.Getenv("JSONSTREAM_OUT"); out != "" {
		if err := os.WriteFile(out, []byte(tr.String()), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	if n == 3000 {
		golden(t, "random", tr.String())
	}
}

// randomPiece: a piece of a stream.
func randomPiece(r *rand.Rand, evs [][]byte) string {
	switch r.Intn(12) {
	case 0, 1, 2:
		return string(evs[r.Intn(len(evs))])
	case 3:
		return []string{"0", "7", "18446744073709551615", "18446744073709551616", "-1", "1.5", "1e3", "01", "-",
			"1e", "00", "123456789012345678901234567890"}[r.Intn(12)]
	case 4:
		return []string{"true", "false", "null", "nul", "tru", "nullx"}[r.Intn(6)]
	case 5:
		return []string{`"x"`, `"a b"`, `""`, `"unterminated`, `"A"`, `"\n"`}[r.Intn(6)]
	case 6:
		return []string{" ", "\n", "\t", "\r\n", "  \n  "}[r.Intn(5)]
	case 7:
		return []string{",", ":", "]", "}", "[", "{", "x", "#"}[r.Intn(8)]
	case 8:
		d := []int{1, 2, 100, 9999, 10000, 10001}[r.Intn(6)]
		return strings.Repeat("[", d) + strings.Repeat("]", d)
	case 9:
		return `{"@type":` + strconv.Itoa(r.Intn(300)) + `,"data":` + []string{"null", "[]", "{}", `"s"`, "123", `{"view_num":"3","request":{"op":"x"}}`}[r.Intn(6)] + "}"
	case 10:
		return `{"view_num":"` + strconv.Itoa(r.Intn(1000)) + `","op_num":"x","VIEW_NUM":"9","request":{"OP":"y"},"zz":[1,{"a":[]}]}`
	}
	return `[` + strings.Repeat(`"filler",`, r.Intn(800)) + `1]`
}
