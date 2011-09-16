SRC_JS = require agda.frp agda.frp.main agda.frp.signal agda.frp.time agda.frp.mixin agda.frp.taskqueue

DEMO_AGDA = FRP.JS.Demo.Clock
DEMO_HTML = clock

DIST_FILES = $(addprefix dist/, \
  $(addsuffix .js,$(SRC_JS)) \
  $(addprefix jAgda.,$(addsuffix .js,$(DEMO_AGDA))) \
  $(addsuffix .html,$(DEMO_HTML)))

dist/:
	mkdir dist

dist/%.html: demo/html/%.html
	cp $< $@

dist/%.js: src/js/%.js
	cp $< $@

.SECONDEXPANSION:
dist/jAgda.%.js: demo/agda/$$(subst .,/,$$*).agda
	agda -i src/agda -i demo/agda --js --compile-dir dist $<

demos: dist/ $(DIST_FILES)
	@echo $(DIST_FILES)

all: demos
