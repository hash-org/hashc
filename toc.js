// Populate the sidebar
//
// This is a script, and not included directly in the page, to control the total size of the book.
// The TOC contains an entry for each page, so if each page includes a copy of the TOC,
// the total size of the page becomes O(n**2).
class MDBookSidebarScrollbox extends HTMLElement {
    constructor() {
        super();
    }
    connectedCallback() {
        this.innerHTML = '<ol class="chapter"><li class="chapter-item expanded "><a href="intro.html"><strong aria-hidden="true">1.</strong> Introduction</a></li><li class="chapter-item expanded "><a href="features/intro.html"><strong aria-hidden="true">2.</strong> Language features</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="features/name-bindings.html"><strong aria-hidden="true">2.1.</strong> Name bindings</a></li><li class="chapter-item expanded "><a href="features/functions.html"><strong aria-hidden="true">2.2.</strong> Functions</a></li><li class="chapter-item expanded "><a href="features/primitives.html"><strong aria-hidden="true">2.3.</strong> Primitives</a></li><li class="chapter-item expanded "><a href="features/control-flow.html"><strong aria-hidden="true">2.4.</strong> 🚧 Control flow</a></li><li class="chapter-item expanded "><a href="features/operators.html"><strong aria-hidden="true">2.5.</strong> 🚧 Operators</a></li><li class="chapter-item expanded "><a href="features/types.html"><strong aria-hidden="true">2.6.</strong> 🚧 Types</a></li><li class="chapter-item expanded "><a href="features/structs-enums.html"><strong aria-hidden="true">2.7.</strong> Structs and enums</a></li><li class="chapter-item expanded "><a href="features/modules.html"><strong aria-hidden="true">2.8.</strong> Modules and visibility</a></li><li class="chapter-item expanded "><a href="features/patterns.html"><strong aria-hidden="true">2.9.</strong> Patterns</a></li><li class="chapter-item expanded "><a href="features/traits-impls.html"><strong aria-hidden="true">2.10.</strong> Traits and implementations</a></li><li class="chapter-item expanded "><a href="features/type-functions.html"><strong aria-hidden="true">2.11.</strong> Type functions</a></li><li class="chapter-item expanded "><a href="features/memory.html"><strong aria-hidden="true">2.12.</strong> 🚧 Memory management</a></li><li class="chapter-item expanded "><a href="features/macros.html"><strong aria-hidden="true">2.13.</strong> 🚧 Macros</a></li></ol></li><li class="chapter-item expanded "><a href="standard-library/intro.html"><strong aria-hidden="true">3.</strong> Standard library</a></li><li class="chapter-item expanded "><a href="interpreter/intro.html"><strong aria-hidden="true">4.</strong> Interpreter</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="interpreter/options.html"><strong aria-hidden="true">4.1.</strong> Interpreter options</a></li><li class="chapter-item expanded "><a href="interpreter/backends.html"><strong aria-hidden="true">4.2.</strong> Compiler backends</a></li></ol></li><li class="chapter-item expanded "><a href="advanced/intro.html"><strong aria-hidden="true">5.</strong> Advanced concepts</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="advanced/compiler-internals.html"><strong aria-hidden="true">5.1.</strong> Compiler internals</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="advanced/loop-transpilation.html"><strong aria-hidden="true">5.1.1.</strong> Loop transpilation</a></li><li class="chapter-item expanded "><a href="advanced/if-statement-transpilation.html"><strong aria-hidden="true">5.1.2.</strong> If statement transpilation</a></li><li class="chapter-item expanded "><a href="advanced/type-inference.html"><strong aria-hidden="true">5.1.3.</strong> Type inference</a></li></ol></li><li class="chapter-item expanded "><a href="advanced/future-features.html"><strong aria-hidden="true">5.2.</strong> Future features</a></li></ol></li></ol>';
        // Set the current, active page, and reveal it if it's hidden
        let current_page = document.location.href.toString();
        if (current_page.endsWith("/")) {
            current_page += "index.html";
        }
        var links = Array.prototype.slice.call(this.querySelectorAll("a"));
        var l = links.length;
        for (var i = 0; i < l; ++i) {
            var link = links[i];
            var href = link.getAttribute("href");
            if (href && !href.startsWith("#") && !/^(?:[a-z+]+:)?\/\//.test(href)) {
                link.href = path_to_root + href;
            }
            // The "index" page is supposed to alias the first chapter in the book.
            if (link.href === current_page || (i === 0 && path_to_root === "" && current_page.endsWith("/index.html"))) {
                link.classList.add("active");
                var parent = link.parentElement;
                if (parent && parent.classList.contains("chapter-item")) {
                    parent.classList.add("expanded");
                }
                while (parent) {
                    if (parent.tagName === "LI" && parent.previousElementSibling) {
                        if (parent.previousElementSibling.classList.contains("chapter-item")) {
                            parent.previousElementSibling.classList.add("expanded");
                        }
                    }
                    parent = parent.parentElement;
                }
            }
        }
        // Track and set sidebar scroll position
        this.addEventListener('click', function(e) {
            if (e.target.tagName === 'A') {
                sessionStorage.setItem('sidebar-scroll', this.scrollTop);
            }
        }, { passive: true });
        var sidebarScrollTop = sessionStorage.getItem('sidebar-scroll');
        sessionStorage.removeItem('sidebar-scroll');
        if (sidebarScrollTop) {
            // preserve sidebar scroll position when navigating via links within sidebar
            this.scrollTop = sidebarScrollTop;
        } else {
            // scroll sidebar to current active section when navigating via "next/previous chapter" buttons
            var activeSection = document.querySelector('#sidebar .active');
            if (activeSection) {
                activeSection.scrollIntoView({ block: 'center' });
            }
        }
        // Toggle buttons
        var sidebarAnchorToggles = document.querySelectorAll('#sidebar a.toggle');
        function toggleSection(ev) {
            ev.currentTarget.parentElement.classList.toggle('expanded');
        }
        Array.from(sidebarAnchorToggles).forEach(function (el) {
            el.addEventListener('click', toggleSection);
        });
    }
}
window.customElements.define("mdbook-sidebar-scrollbox", MDBookSidebarScrollbox);
