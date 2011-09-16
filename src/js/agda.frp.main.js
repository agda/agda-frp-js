require(["agda.frp"],function(frp) { require.ready(function() {
    var nodes = document.getElementsByClassName("agda");
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