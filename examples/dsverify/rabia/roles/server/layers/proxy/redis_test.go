/*
    Copyright 2021 Rabia Research Team and Developers

    Licensed under the Apache License, Version 2.0 (the "License");
    you may not use this file except in compliance with the License.
    You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

    Unless required by applicable law or agreed to in writing, software
    distributed under the License is distributed on an "AS IS" BASIS,
    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
    See the License for the specific language governing permissions and
    limitations under the License.
*/
package proxy

import (
	"context"
	"fmt"
	"github.com/go-redis/redis/v8"
	"net"
	"rabia/internal/config"
	"rabia/internal/message"
	"testing"
)

var ctx = context.Background()

func TestRedis(t *testing.T) {
	redisUp(t)
	rdb := redis.NewClient(&redis.Options{
		Addr:     "localhost:6379",
		Password: "", // no password set
		DB:       0,  // use default DB
	})

	err := rdb.Set(ctx, "key", "value", 0).Err()
	if err != nil {
		panic(err)
	}

	val, err := rdb.Get(ctx, "key").Result()
	if err != nil {
		panic(err)
	}
	if val != "value" {
		t.Error("error here 1")
	}
	t.Log("key", val)

	val2, err := rdb.Get(ctx, "key2").Result()
	if err == redis.Nil {
		fmt.Println("key2 does not exist")
	} else if err != nil {
		panic(err)
	} else {
		fmt.Println("key2", val2)
	}
	// Output: key value
	// key2 does not exist
}

func TestProxy_RedisBatchExecuteCmd(t *testing.T) {
	redisUp(t)
	config.Conf.StorageMode = 2
	config.Conf.RedisAddr = []string{"localhost:6379", "localhost:6380", "localhost:6381"}
	config.Conf.ProxyBatchSize = 5
	config.Conf.ClientBatchSize = 2
	config.Conf.KeyLen = 2
	config.Conf.ValLen = 2

	p := Proxy{
		RedisClient: RedisInit(0),
		RedisCtx:    context.Background(),
	}

	dec1 := &message.ConsensusObj{
		CliIds:  []uint32{0, 0, 0, 1, 1},
		CliSeqs: []uint32{1000, 1001, 1002, 2000, 2001},
		Commands: []string{"0k1v1", "1k2", "0k3v3", "1k4", "0k5v5",
			"1k6", "0k7v7", "1k3", "0k9v9", "1k1"},
	}

	p.CurrDec = dec1
	res := p.RedisBatchExecuteCmd()
	for _, re := range res {
		fmt.Println(re)
	}

	dec2 := &message.ConsensusObj{
		CliIds:  []uint32{1, 1, 1, 2, 2},
		CliSeqs: []uint32{2002, 2003, 2004, 1000, 1001},
		Commands: []string{"0k2v2", "1k2", "0k4v4", "1k4", "0k5v5",
			"1k5", "0k6v6", "1k6", "0k7v7", "1k7"},
	}
	p.CurrDec = dec2
	res = p.RedisBatchExecuteCmd()
	for _, re := range res {
		fmt.Println(re)
	}

}
// redisUp skips the test unless a Redis server listens at localhost:6379 (etcd-grove: upstream's
// tests need one; the lab ran them against its go-redis model).
func redisUp(t *testing.T) {
	if c, err := net.Dial("tcp", "localhost:6379"); err != nil {
		t.Skip("no Redis server at localhost:6379")
	} else {
		c.Close()
	}
}
