
MAIN = volume5
TEXBIN = /Library/TeX/texbin
LOCK = .build.lock

# Collision-safe build. Multiple RYOT seats and the operator may invoke `make all`
# in this same directory at once; concurrent latexmk/biber runs then collide on
# volume5.bcf and leave a transient volume5.bcf-SAVE-ERROR (a self-healing failure
# the operator sees as "build broke"). macOS has no flock, so serialize with a
# portable *atomic* mkdir lock:
#   - mkdir is atomic, so there is no check-then-act race (unlike pgrep guards);
#   - if the lock is held, skip (benign — the in-flight build produces the PDF);
#   - a lock older than 10 min is a crashed build's orphan -> break it (never wedges);
#   - always release on exit (normal, interrupt, or error);
#   - latexmk's exit code is preserved so real failures still surface.
all:
	@if [ -d $(LOCK) ] && [ -z "`find $(LOCK) -mmin -10 2>/dev/null`" ]; then \
	  echo "[make] breaking stale build lock ($(LOCK), >10 min old)"; rmdir $(LOCK) 2>/dev/null || true; fi
	@if ! mkdir $(LOCK) 2>/dev/null; then echo "[make] a $(MAIN) build is already running; skipping"; exit 0; fi; \
	trap 'rmdir $(LOCK) 2>/dev/null || true' EXIT INT TERM; \
	$(TEXBIN)/latexmk -pdf -interaction=nonstopmode -halt-on-error $(MAIN).tex

clean:
	$(TEXBIN)/latexmk -C
	@rmdir $(LOCK) 2>/dev/null || true

distclean: clean
	rm -f $(MAIN).pdf

.PHONY: all clean distclean
