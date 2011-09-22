SRC_JS = require agda.frp agda.frp.main agda.frp.signal agda.frp.time agda.frp.mixin agda.frp.taskqueue

DEMO_AGDA = FRP.JS.Demo.Hello FRP.JS.Demo.Clock FRP.JS.Demo.Button FRP.JS.Demo.Calculator FRP.JS.Demo.Geolocation
DEMO_HTML = hello clock button calculator geolocation
DEMO_CSS = demo
DEMO_PNG = alu

DIST_FILES = $(addprefix dist/, \
  $(addsuffix .js,$(SRC_JS)) \
  $(addprefix jAgda.,$(addsuffix .js,$(DEMO_AGDA))) \
  $(addsuffix .html,$(DEMO_HTML)) \
  $(addsuffix .css,$(DEMO_CSS)) \
  $(addsuffix .png,$(DEMO_PNG)))

dist/:
	mkdir dist

dist/%.html: demo/html/%.html
	cp $< $@

dist/%.css: demo/css/%.css
	cp $< $@

dist/%.png: demo/images/%.png
	cp $< $@

dist/%.js: src/js/%.js
	cp $< $@

.SECONDEXPANSION:
dist/jAgda.%.js: demo/agda/$$(subst .,/,$$*).agda src/agda/FRP/JS/*.agda src/agda/FRP/JS/*/*.agda demo/agda/FRP/JS/Demo/*.agda demo/agda/FRP/JS/Demo/*/*.agda
	agda -i src/agda -i demo/agda --js --compile-dir dist $<

demos: dist/ $(DIST_FILES)

all: demos
