# Requirements on `go_etcd_io_etcd_server_v3_storage_schema`

## from 2e

Provisional, to be replaced by 4b's names:
1. `Membership.beMembers mb st` (the `MembershipBackend`'s member and removed buckets hold `st`),
   which `RaftCluster.SetBackend` turns into the cluster's `beView c st`; `MustSaveMemberToBackend`,
   `MustDeleteMemberFromBackend`, `MustReadMembersFromBackend` move/read it as the writers do.
2. `V3alarm.beAlarms be al` / `V3alarm.alarmBe ab al` (the alarm bucket; `NewAlarmBackend(lg, be)`
   turns the first into the second); `MustPutAlarm`, `MustDeleteAlarm`, `GetAllAlarms`.
Used by `RaftCluster.*.spec`, `NewAlarmStore.spec`, `AlarmStore.Recover.spec`, `restoreAlarms.spec`.
