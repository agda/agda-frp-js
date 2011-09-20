require(["agda.frp"],function(frp) { require.ready(function() {
    window.scrollTo(0,1);
    var nodes;
    if (document.getElementsByClassName) {
	nodes = document.getElementsByClassName("agda");
    } else {
	nodes = [];
	function iterate(children) {
	    if (children) {
		for (var i = 0; i < children.length; i++) {
		    var node = children[i];
		    if ((node.className === "agda") || (node.getAttribute && node.getAttribute("class") === "agda")) { 
			nodes.push(node);
		    }
		    iterate(node.children);
		}
	    }
	}
	iterate(document.childNodes);
    }
    for (var i = 0; i < nodes.length; i++) {
	var node = nodes[i];
	var agdaName = node.getAttribute("data-agda");
	var agdaMain = node.getAttribute("data-agda-main") || "main";
	if (agdaName) {
	    var jsName = "jAgda." + agdaName;
	    require([jsName],function(jsModule) {
		var jsMain = jsModule[agdaMain];
		frp.reactimate(jsMain).attachTo(node);
	    });
	}
    }
}); });