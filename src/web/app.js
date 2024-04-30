
function on_click_node(ev) {
	const popover = document.getElementById("object-label");
	// popover.popoverTargetElement = 
	popover.showModal();

	// Walk up the target to the G node:
	let target = ev.target;
	while (target.nodeName != "g") {
		target = target.parentElement;
	}
	// Then find the first text log, to get the node name...
	let nodename = "";
	for (const child of target.childNodes) {
		if (child.nodeName === "text") {
			nodename = child.innerHTML;
			break;
		}
	}
	// Set the hidden input:
	//
	// TODO: Set object in hiddden input
	const hidden = document.getElementById("object_id");
	hidden.value = nodename;

	console.log("node was clicked: ", ev)
	console.log("set input: ", hidden)
}

function attach_callbacks() {
	for (const object_node of document.querySelectorAll("g.node")) {
		object_node.addEventListener("click", on_click_node);
	}
	console.log("attached callbacks");
}

attach_callbacks();
