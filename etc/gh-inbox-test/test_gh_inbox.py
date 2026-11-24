#!/usr/bin/env python3
"""Tests of etc/gh-inbox.py on recorded JSON (no network):

    python3 -m unittest discover -s etc/gh-inbox-test      (or: python3 etc/gh-inbox-test/test_gh_inbox.py)

fixtures/legacy-comments.json and perennial-pulls.json are API responses recorded on 2026-11-23
(trimmed to the fields the tool reads); fixtures/convention-comments.json are posts in the
convention of notes/coordination.md, in the same API shape."""
import contextlib, datetime, importlib.util, io, json, os, tempfile, unittest, urllib.error
from email.message import Message

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("gh_inbox", os.path.join(HERE, "..", "gh-inbox.py"))
gi = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gi)

REG = gi.Registry.load(os.path.join(HERE, "..", "sessions.txt"))


def fixture(name):
    with open(os.path.join(HERE, "fixtures", name)) as f:
        return json.load(f)


LEGACY = {str(c["id"]): gi.norm_comment(c, "etcd-grove") for c in fixture("legacy-comments.json")}
CONV = {str(c["id"]): gi.norm_comment(c, "etcd-grove") for c in fixture("convention-comments.json")}
PULLS = [gi.norm_pull(p, "perennial") for p in fixture("perennial-pulls.json")]
NOW = gi.ts("2026-11-24T06:00:00Z")


def model(*ids, pulls=(), upto=None):
    posts = [(LEGACY.get(i) or CONV[i]) for i in ids]
    if upto:
        posts = [p for p in posts if p["created"] <= upto]
    return gi.Model(REG, posts, list(pulls))


def tags(lines):
    return [l.split("[", 1)[1].split("]", 1)[0] for l in lines]


class Registry(unittest.TestCase):
    def test_rows(self):
        self.assertEqual(REG.canon("COORDINATOR-e"), "coordinator-E")
        self.assertEqual(REG.landers("mit-pdos/perennial"), ["coordinator-E"])
        self.assertEqual(sorted(REG.queue_handles()), ["zeldovich-coordinator", "zeldovich-proving-2"])
        self.assertEqual(REG.get("dsverify-net").sigs, ["upamanyus session (dsverify-net"])
        self.assertTrue(REG.get("upamanyus").human)

    def test_double_bar_separates_signatures(self):
        r = gi.Registry.parse("x | o | m | acc | relay | sig one || sig two | alias a || alias b\n# c\n")
        self.assertEqual(r.get("x").sigs, ["sig one", "sig two"])
        self.assertEqual(r.get("x").aliases, ["alias a", "alias b"])


class Parsing(unittest.TestCase):
    def test_to_from_and_actions(self):
        p = gi.Post(CONV["9000000002"])
        self.assertEqual(p.to, ["zeldovich-coordinator"])   # the (@account) is for notifications
        self.assertEqual(p.frm, "coordinator-E")
        self.assertEqual(p.actions(), [("ack", ["9000000001"], "checking with Upamanyu", [])])
        p = gi.Post(CONV["9000000004"])
        self.assertEqual(p.actions(), [("done", ["9000000001"], "four is fine; Upamanyu agrees.", [])])

    def test_ids_in_links(self):
        self.assertEqual(gi.norm_id("https://github.com/mit-pdos/etcd-grove/issues/8#issuecomment-7116863161"),
                         "7116863161")
        self.assertEqual(gi.norm_id("issuecomment-7116863161"), "7116863161")
        self.assertEqual(gi.norm_id("https://github.com/mit-pdos/perennial/pull/688"), "perennial#688")
        self.assertIsNone(gi.norm_id("7896dc22d1"))   # a sha is not an id

    def test_lines_in_code_and_quotes_do_not_count(self):
        p = gi.Post(dict(CONV["9000000002"], body="```\nask: not this\n```\n> done: 9000000001\nhello"))
        self.assertEqual(p.lines, [])


class MisFilter(unittest.TestCase):
    """Watching as coordinator-E: posts addressed to "coordinator-E" are never taken for its own."""

    def setUp(self):
        self.w = gi.Watcher(REG, "coordinator-E", None)
        self.w.step(model(), NOW)   # a first run with nothing: from now on everything is new

    def test_mentions_are_not_mine(self):
        ids = ["7115229276", "7116775758", "7116787559", "7116863161",
               "9000000010", "9000000011", "9000000012", "9000000013"]
        out = self.w.step(model(*ids), NOW)
        printed = {l.split()[3] for l in out}
        # kaashoek's legacy posts "@upamanyus-agent (coordinator-E): ..." are for me
        self.assertIn("7115229276", printed)
        self.assertIn("7116787559", printed)
        # a post quoting my old signature is still someone else's
        self.assertIn("9000000010", printed)
        # `to: coordinator-E` from another session of the same account
        self.assertIn("9000000012", printed)
        # mine: my legacy signature (7116775758, 7116863161) or my `from:` line (9000000011),
        # although both name coordinator-E; and a `to:` post to someone else only names me
        for mine in ("7116775758", "7116863161", "9000000011", "9000000013"):
            self.assertNotIn(mine, printed)
        self.assertEqual(sorted(tags(out)), ["legacy-mention", "legacy-mention", "legacy-mention", "to-me"])

    def test_the_other_side_sees_my_post(self):
        w = gi.Watcher(REG, "zeldovich-coordinator", None)
        w.step(model(), NOW)
        out = w.step(model("9000000011", "9000000013"), NOW)
        self.assertEqual(tags(out), ["to-me"])


class Asks(unittest.TestCase):
    IDS = ["9000000001", "9000000002", "9000000003", "9000000004"]

    def test_acked_then_closed_by_re_done(self):
        m = model(*self.IDS, upto="2026-11-24T01:00:00Z")
        it = m.items["9000000001"]
        self.assertEqual((it.state, it.to, it.asker), ("open", ["coordinator-E"], "zeldovich-coordinator"))
        self.assertEqual([i.id for i in m.open_items("coordinator-E")], ["9000000001"])
        m = model(*self.IDS, upto="2026-11-24T01:06:00Z")
        it = m.items["9000000001"]
        self.assertEqual((it.state, it.owner), ("acked", "coordinator-E"))   # still listed, with its owner
        self.assertIn("owner coordinator-E", m.open_items("coordinator-E")[0].line(NOW))
        self.assertIn("ignored", it.history[-1][2])   # dsverify-lab is neither addressee nor asker
        m = model(*self.IDS)
        it = m.items["9000000001"]
        self.assertEqual((it.state, it.how, it.closed_by), ("closed", "done", "coordinator-E"))
        self.assertEqual(m.open_items("coordinator-E"), [])

    def test_watch_prints_each_change_once(self):
        a = gi.Watcher(REG, "coordinator-E", None)
        z = gi.Watcher(REG, "zeldovich-coordinator", None)
        for w in (a, z):
            w.step(model(), NOW)
        steps = ["2026-11-24T01:00:00Z", "2026-11-24T01:06:00Z", "2026-11-24T01:20:00Z"]
        got = {"a": [], "z": []}
        for t in steps:
            got["a"].append(tags(a.step(model(*self.IDS, upto=t), NOW)))
            got["z"].append(tags(z.step(model(*self.IDS, upto=t), NOW)))
        self.assertEqual(got["a"], [["ask"], [], []])   # its own ack and answer are not news to it
        # the asker sees its ask acked and answered; dsverify-lab's ignored done changes nothing
        self.assertEqual(got["z"], [[], ["acked", "to-me"], ["closed"]])
        self.assertEqual(a.step(model(*self.IDS), NOW), [])

    def test_superseded_and_withdrawn(self):
        m = model("9000000005", "9000000006", "9000000007")
        old, new = m.items["9000000005"], m.items["9000000006"]
        self.assertEqual((old.state, old.how, old.superseded_by), ("closed", "superseded", ["9000000006"]))
        self.assertEqual((new.state, new.how), ("closed", "withdrawn"))   # the asker withdrew it
        m = model("9000000005", "9000000006")
        self.assertEqual([i.id for i in m.open_items("upamanyus")], ["9000000006"])

    def test_digest_for_the_human(self):
        m = model("9000000005", "9000000006", "9000000008", "9000000009", pulls=PULLS)
        d = gi.digest(m, "upamanyus", NOW)
        self.assertIn("Waiting on upamanyus: 3", d)
        self.assertIn("swiftpaxos prophecy", d)
        self.assertIn("`review:perennial#661:upamanyus`", d)
        self.assertNotIn("9000000005", d)   # superseded
        self.assertNotIn("gods-verified", d)   # a decision for dsverify-lab, not for him
        self.assertEqual([i.kind for i in m.open_items("dsverify-lab")], ["decision"])
        # coordinator-E relays for Upamanyu, so it sees what is addressed to him
        self.assertIn("9000000008", [i.id for i in m.open_items("coordinator-E")])


class Legacy(unittest.TestCase):
    def test_scan_proposes_an_unanswered_legacy_ask(self):
        m = model("7115229276")   # "... Approve, and OK to queue?" to coordinator-E, unsigned convention
        out = gi.scan(m, "2026-11-23T00:00:00Z", NOW)
        self.assertEqual(len(out), 1)
        self.assertIn("7115229276 etcd-grove#8", out[0])
        self.assertIn("from dsverify-lab to coordinator-E", out[0])
        self.assertIn("Approve, and OK to queue?", out[0])
        self.assertEqual(m.items, {})   # a proposal only: no item until someone posts the ask

    def test_scan_skips_answered_ones(self):
        m = model("7115229276", "7116775758")   # coordinator-E answered later in the thread...
        out = gi.scan(m, "2026-11-23T00:00:00Z", NOW)
        self.assertNotIn("7115229276", " ".join(out))
        # ... with a legacy ask of its own: "please confirm the head you want reviewed"
        self.assertEqual(len(out), 1)
        self.assertIn("7116775758 etcd-grove#8 age 6h43m from coordinator-E to dsverify-lab:", out[0])
        m = model("7115229276", "9000000003")   # a later post by the asker is no answer
        self.assertEqual(len(gi.scan(m, "2026-11-23T00:00:00Z", NOW)), 1)

    def test_authors_of_legacy_posts(self):
        m = model("7115229276", "7116863161", "7116328439", "7116430850")
        self.assertEqual(m.author["7115229276"], "dsverify-lab")   # by signature, not by login
        self.assertEqual(m.author["7116863161"], "coordinator-E")
        self.assertEqual(m.author["7116328439"], "zeldovich-coordinator")
        self.assertEqual(m.author["7116430850"], "zeldovich-coordinator")


class PullRequests(unittest.TestCase):
    def test_collaborator_prs_wait_on_the_lander(self):
        m = model(pulls=PULLS)
        land = sorted(i.id for i in m.items.values() if i.kind == "land")
        # 694 is a draft and 687 is by our account; dependabot's 635 is a bot's
        self.assertEqual(land, ["land:perennial#661", "land:perennial#688", "land:perennial#690"])
        self.assertEqual(m.items["land:perennial#688"].to, ["coordinator-E"])
        self.assertEqual(m.items["review:perennial#661:upamanyus"].to, ["upamanyus"])
        # the author's session sees what it waits on
        self.assertIn("land:perennial#688", [i.id for i in m.open_items(by="dsverify-lab")])

    def test_flagged_acked_and_gone(self):
        w = gi.Watcher(REG, "coordinator-E", None)
        out = w.step(model(pulls=PULLS), NOW)
        self.assertIn("[open] land:perennial#688", " ".join(out))
        author = gi.Watcher(REG, "dsverify-lab", None)   # kaashoek's PR: its session waits on it
        self.assertIn("[waiting] land:perennial#688", " ".join(author.step(model(pulls=PULLS), NOW)))
        ack = dict(CONV["9000000011"], id="9000000020", created="2026-11-24T05:00:00Z",
                   body="to: dsverify-lab\n\nack: land:perennial#688 landing it after the build\n\nfrom: coordinator-E")
        m = gi.Model(REG, [ack], PULLS)
        self.assertEqual((m.items["land:perennial#688"].state, m.items["land:perennial#688"].owner),
                         ("acked", "coordinator-E"))
        self.assertEqual(tags(w.step(m, NOW)), [])
        self.assertEqual(tags(author.step(m, NOW)), ["acked"])
        merged = [p for p in PULLS if p["number"] != 688]   # the PR is merged: gone from the open list
        out = w.step(gi.Model(REG, [ack], merged), NOW)
        self.assertEqual(out[0].split("] ", 1)[1], "land:perennial#688 no longer open on GitHub")
        bumped = [dict(p, updated="2026-11-24T05:30:00Z") if p["number"] == 690 else p for p in merged]
        self.assertEqual(tags(w.step(gi.Model(REG, [ack], bumped), NOW)), ["pr-updated"])


class Queue(unittest.TestCase):
    IDS = ["9000000014", "7116328439", "7116430850", "7116439402", "7116754079"]

    def test_failure_goes_back_to_the_asker_and_landed_closes_it(self):
        it = model(*self.IDS, upto="2026-11-23T22:50:00Z").items["queue:net-sticky-read"]
        self.assertEqual((it.state, it.to, it.asker),
                         ("open", ["zeldovich-coordinator", "zeldovich-proving-2"], "dsverify-net"))
        it = model(*self.IDS, upto="2026-11-23T22:55:00Z").items["queue:net-sticky-read"]
        self.assertEqual((it.state, it.owner), ("acked", "zeldovich-coordinator"))   # "Enqueued"
        it = model(*self.IDS, upto="2026-11-23T23:00:00Z").items["queue:net-sticky-read"]
        self.assertEqual((it.state, it.to), ("open", ["dsverify-net"]))   # "did not land"
        it = model(*self.IDS).items["queue:net-sticky-read"]
        self.assertEqual((it.state, it.how), ("closed", "landed"))

    def test_watch_for_the_branch_owner(self):
        w = gi.Watcher(REG, "dsverify-net", None)
        w.step(model(), NOW)
        seen = []
        for t in ["2026-11-23T22:50:00Z", "2026-11-23T22:55:00Z", "2026-11-23T23:00:00Z", "2026-11-23T23:16:00Z"]:
            seen.append(tags(w.step(model(*self.IDS, upto=t), NOW)))
        self.assertEqual(seen, [[], ["acked"], ["land-queue"], ["closed"]])

    def test_queue_lines_are_read_as_they_are(self):
        p = gi.Post(LEGACY["7116787559"])   # "land-queue: gods-verified 74c9904d8c" inside a legacy post
        self.assertEqual(p.queue, [("gods-verified", "74c9904d8c")])
        m = model("7116787559", "7116832119")
        self.assertEqual(m.items["queue:gods-verified"].state, "acked")

    def test_failure_then_resent_then_requeued_in_bulk(self):
        ids = ["7116787559", "7116832119", "7117114829", "7117127495", "7117157454"]
        it = model(*ids, upto="2026-11-23T23:34:25Z").items["queue:gods-verified"]
        self.assertEqual((it.state, it.to, it.asker), ("open", ["dsverify-lab"], "dsverify-lab"))
        it = model(*ids, upto="2026-11-23T23:35:06Z").items["queue:gods-verified"]
        self.assertEqual((it.state, it.to[0]), ("open", "zeldovich-coordinator"))   # re-sent to the queue
        it = model(*ids).items["queue:gods-verified"]   # "All eight are re-queued ...: ..., `gods-verified`"
        self.assertEqual((it.state, it.owner), ("acked", "zeldovich-coordinator"))

    def test_vm_build(self):
        m = model("7115796115", "7115818074", upto="2026-11-23T22:29:22Z")
        it = m.items["vm-build:net-sticky-read@902ce91edb"]
        self.assertEqual((it.state, it.owner, it.asker), ("acked", "zeldovich-coordinator", "dsverify-net"))
        it = model("7115796115", "7115818074", "7115904374").items["vm-build:net-sticky-read@902ce91edb"]
        self.assertEqual((it.state, it.how), ("closed", "finished"))


class Posting(unittest.TestCase):
    def test_header_and_footer(self):
        body = gi.build_post(REG, "coordinator-E", ["zeldovich-coordinator", "upamanyus"], "Hello.\n", ask="OK?")
        self.assertEqual(body, "to: zeldovich-coordinator, upamanyus (@zeldovich-agent @upamanyus)\n\n"
                               "Hello.\n\nask: OK?\n\nfrom: coordinator-E\n")
        p = gi.Post({"id": "1", "repo": "etcd-grove", "number": 8, "kind": "comment", "login": "upamanyus-agent",
                     "url": "", "created": "2026-11-24T00:00:00Z", "updated": "", "body": body})
        self.assertEqual((p.to, p.frm), (["zeldovich-coordinator", "upamanyus"], "coordinator-E"))

    def test_refusals(self):
        with self.assertRaises(SystemExit):
            gi.build_post(REG, "coordinator-E", ["coordinator-F"], "x")
        with self.assertRaises(SystemExit):
            gi.build_post(REG, "coordinator-E", ["all"], "to: all\nx")
        with self.assertRaises(SystemExit):
            gi.build_post(REG, "coordinator-E", ["all"], "no ask line", ask=True)

    def test_post_writes_a_file_and_never_posts(self):
        with tempfile.TemporaryDirectory() as d:
            f = os.path.join(d, "b.md")
            with open(f, "w") as fh:
                fh.write("ask: ready?\n")
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                rc = gi.main(["post", "--me", "dsverify-net", "--to", "coordinator-E", "--issue", "24", f, "--ask"])
            self.assertEqual(rc, 0)
            with open(f + ".post") as fh:
                self.assertTrue(fh.read().startswith("to: coordinator-E\n"))   # same account: no @
            self.assertIn(f"gh api repos/mit-pdos/etcd-grove/issues/24/comments -F body=@{f}.post",
                          buf.getvalue())


class FakeResponse:
    def __init__(self, body, headers):
        self.body, self.headers = body, headers

    def read(self):
        return self.body

    def __enter__(self):
        return self

    def __exit__(self, *a):
        return False


def headers(**kw):
    m = Message()
    for k, v in kw.items():
        m[k.replace("_", "-")] = v
    return m


class Http(unittest.TestCase):
    def test_etag_pages_and_backoff(self):
        token = "ghp_secretsecretsecret"
        calls, slept = [], []
        script = [
            ("200", b'[{"n": 1}]', headers(ETag='"a"', Link='<https://api.github.com/x?page=2>; rel="next"')),
            ("200", b'[{"n": 2}]', headers(ETag='"b"')),
            ("304", None, headers()),   # page 1 unchanged: its cached body and next link
            ("403", None, headers(X_RateLimit_Remaining="0", X_RateLimit_Reset="0")),   # back off, retry
            ("304", None, headers()),
        ]

        def opener(req, timeout):
            calls.append(req)
            code, body, h = script[len(calls) - 1]
            if code == "200":
                return FakeResponse(body, h)
            raise urllib.error.HTTPError(req.full_url, int(code), "x", h, io.BytesIO(b""))

        with tempfile.TemporaryDirectory() as d:
            gh = gi.GitHub(token, d, opener=opener, sleep=slept.append, log=lambda s: None)
            self.assertEqual(gh.pages("x", page=1), [{"n": 1}, {"n": 2}])
            self.assertEqual(gh.pages("x", page=1), [{"n": 1}, {"n": 2}])
            self.assertEqual(calls[2].get_header("If-none-match"), '"a"')
            self.assertEqual(calls[3].get_header("If-none-match"), '"b"')
            self.assertEqual(len(slept), 1)
            self.assertEqual(gh.not_modified, 2)
            for root, _, files in os.walk(d):   # the token is never written
                for f in files:
                    with open(os.path.join(root, f)) as fh:
                        self.assertNotIn(token, fh.read())

    def test_store_cursor(self):
        seen = []

        class GH:
            def pages(self, path, **params):
                seen.append((path, params.get("since")))
                if path.endswith("issues/comments") and "etcd-grove" in path:
                    return [fixture("legacy-comments.json")[0]]
                return []

        with tempfile.TemporaryDirectory() as d:
            st = gi.Store(d)
            st.sync(GH(), "2026-11-01T00:00:00Z")
            st2 = gi.Store(d)   # a restart resumes from the newest update seen, not from "now"
            st2.sync(GH(), "2026-11-24T00:00:00Z")
            self.assertIn(("repos/mit-pdos/etcd-grove/issues/comments", "2026-11-23T22:01:38Z"), seen[9:])
            self.assertEqual(list(st2.posts), ["7115229276"])


if __name__ == "__main__":
    unittest.main()
