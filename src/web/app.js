
function on_click_node(ev) {
	console.log("node was clicked: ", ev)
}

function attach_callbacks() {
	for (const object_node of document.querySelectorAll("g .node")) {
		object_node.addEventListener("click", on_click_node);
	}
	console.log("attached callbacks");
}

attach_callbacks();
