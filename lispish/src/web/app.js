
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
	let existing_label = "";
	for (const child of target.childNodes) {
		if (child.nodeName !== "text") {
			continue;
		}
		if (nodename === "") {
			nodename = child.innerHTML;
			continue;
		}
		// TODO: Not accurate! This might be the value, not a label,
		// if there is no existing label.
		// How do we tell? ...we can't get it structurally, so we may have to use the hack:
		if (child.getAttribute("font-weight") === "bold") {
			existing_label = child.innerHTML;
			break;
		}
	}
	const hidden = document.getElementById("popup_object_id");
	hidden.value = nodename;
	const label = document.getElementById("popup_label");
	label.value = existing_label;


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
