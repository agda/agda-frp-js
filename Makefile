SRC_JS = require agda.frp agda.frp.signal agda.frp.time agda.frp.mixin agda.frp.taskqueue

DEMO_AGDA = FRP.JS.Demo.Clock
DEMO_HTML = clock
DEMO_JS = clock 

DIST_FILES = $(addprefix dist/, \
  $(addprefix jAgda.,$(addsuffix .js,$(DEMO_AGDA))) \
  $(addsuffix .html,$(DEMO_HTML)) \
  $(addsuffix .js,$(SRC_JS) $(DEMO_JS)))

dist/:
	mkdir dist

dist/%.html: demo/html/%.html
	cp $< $@

dist/%.js: demo/js/%.js
	cp $< $@

dist/%.js: src/js/%.js
	cp $< $@

.SECONDEXPANSION:
dist/jAgda.%.js: demo/agda/$$(subst .,/,$$*).agda
	agda -i src/agda -i demo/agda --js --compile-dir dist $<

demos: dist/ $(DIST_FILES)
	@echo $(DIST_FILES)

all: demos
