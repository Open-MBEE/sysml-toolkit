"""Implied-conformance reachability and stale-handle guards."""
import pathlib
import tempfile
import sysmlv2

# Implied conformance is additive; both element arguments remain guarded.
with tempfile.TemporaryDirectory() as library_dir:
    pathlib.Path(library_dir, "Parts.kerml").write_text(
        "standard library package Parts { class Part; }", encoding="utf-8"
    )
    implied_session = sysmlv2.Session.from_sources([("p.sysml", "package P { part def Box; }")])
    stale_box = implied_session.resolve("P::Box")
    implied_session.load_library(library_dir)
    box = implied_session.resolve("P::Box")
    part = implied_session.resolve("Parts::Part")
    assert not implied_session.conforms(box, part)
    assert implied_session.conforms_with_implied(box, part)
    for source, target in [(stale_box, part), (box, stale_box)]:
        try:
            implied_session.conforms_with_implied(source, target)
            raise AssertionError("stale argument must raise")
        except ValueError:
            pass

print("implied conformance: passed")
