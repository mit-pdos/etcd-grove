package gryffcommon

import (
  "gryff/src/gryffproto"
)

type IRMWHandler interface {
  Loop(slowClockChan chan bool)
  HandleRMW(rmw *gryffproto.RMW)
}
