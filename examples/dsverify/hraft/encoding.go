// Copyright IBM Corp. 2013, 2025
// SPDX-License-Identifier: MPL-2.0

package raft

// The verification fork's encoding of configurations and old-format peer lists, in place of MsgPack (reflection):
// unsigned integers as 8 bytes, little-endian; byte strings length-prefixed; lists count-prefixed. Decoding returns
// an error on truncated input, as MsgPack's decoder does.

import "errors"

var errShortBuffer = errors.New("encoding: short buffer")

func appendUint64(b []byte, x uint64) []byte {
	for i := 0; i < 8; i++ {
		b = append(b, byte(x>>(8*uint64(i))))
	}
	return b
}

func appendBytes(b []byte, s []byte) []byte {
	return append(appendUint64(b, uint64(len(s))), s...)
}

func readUint64(b []byte) (uint64, []byte, error) {
	if len(b) < 8 {
		return 0, b, errShortBuffer
	}
	var x uint64
	for i := 0; i < 8; i++ {
		x |= uint64(b[i]) << (8 * uint64(i))
	}
	return x, b[8:], nil
}

func readBytes(b []byte) ([]byte, []byte, error) {
	n, rest, err := readUint64(b)
	if err != nil {
		return nil, b, err
	}
	if uint64(len(rest)) < n {
		return nil, b, errShortBuffer
	}
	out := make([]byte, n)
	copy(out, rest[:n])
	return out, rest[n:], nil
}

// encodeConfigurationBytes and decodeConfigurationBytes replace MsgPack's encoding of a Configuration.
func encodeConfigurationBytes(c Configuration) []byte {
	b := appendUint64(nil, uint64(len(c.Servers)))
	for _, s := range c.Servers {
		b = appendUint64(b, uint64(s.Suffrage))
		b = appendBytes(b, []byte(s.ID))
		b = appendBytes(b, []byte(s.Address))
	}
	return b
}

func decodeConfigurationBytes(b []byte) (Configuration, error) {
	n, b, err := readUint64(b)
	if err != nil {
		return Configuration{}, err
	}
	var servers []Server
	for i := uint64(0); i < n; i++ {
		var suf uint64
		var id, addr []byte
		if suf, b, err = readUint64(b); err != nil {
			return Configuration{}, err
		}
		if id, b, err = readBytes(b); err != nil {
			return Configuration{}, err
		}
		if addr, b, err = readBytes(b); err != nil {
			return Configuration{}, err
		}
		servers = append(servers, Server{Suffrage: ServerSuffrage(suf), ID: ServerID(id), Address: ServerAddress(addr)})
	}
	return Configuration{Servers: servers}, nil
}

// encodePeerList and decodePeerList replace MsgPack's encoding of a [][]byte (the old peers format).
func encodePeerList(peers [][]byte) []byte {
	b := appendUint64(nil, uint64(len(peers)))
	for _, p := range peers {
		b = appendBytes(b, p)
	}
	return b
}

func decodePeerList(b []byte) ([][]byte, error) {
	n, b, err := readUint64(b)
	if err != nil {
		return nil, err
	}
	var peers [][]byte
	for i := uint64(0); i < n; i++ {
		var p []byte
		if p, b, err = readBytes(b); err != nil {
			return nil, err
		}
		peers = append(peers, p)
	}
	return peers, nil
}
