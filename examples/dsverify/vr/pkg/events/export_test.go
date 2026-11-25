package events

import "encoding/json"

// SwapFrameDecoderForTest installs f as the frame decoder and returns the previous one (tests
// only: the released path is the nil decoder).
func SwapFrameDecoderForTest(f func(dec *json.Decoder) (uint8, json.RawMessage, error)) func(dec *json.Decoder) (uint8, json.RawMessage, error) {
	frameDecoderMu.Lock()
	old := frameDecoder
	frameDecoder = f
	frameDecoderMu.Unlock()
	return old
}
