// Form - Updated December 21, 2023
function noop() { }
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert(target, node, anchor) {
    target.insertBefore(node, anchor || null);
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function prevent_default(fn) {
    return function (event) {
        event.preventDefault();
        // @ts-ignore
        return fn.call(this, event);
    };
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
/**
 * List of attributes that should always be set through the attr method,
 * because updating them through the property setter doesn't work reliably.
 * In the example of `width`/`height`, the problem is that the setter only
 * accepts numeric values, but the attribute can also be set to a string like `50%`.
 * If this list becomes too big, rethink this approach.
 */
const always_set_through_set_attribute = ['width', 'height'];
function set_attributes(node, attributes) {
    // @ts-ignore
    const descriptors = Object.getOwnPropertyDescriptors(node.__proto__);
    for (const key in attributes) {
        if (attributes[key] == null) {
            node.removeAttribute(key);
        }
        else if (key === 'style') {
            node.style.cssText = attributes[key];
        }
        else if (key === '__value') {
            node.value = node[key] = attributes[key];
        }
        else if (descriptors[key] && descriptors[key].set && always_set_through_set_attribute.indexOf(key) === -1) {
            node[key] = attributes[key];
        }
        else {
            attr(node, key, attributes[key]);
        }
    }
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function find_comment(nodes, text, start) {
    for (let i = start; i < nodes.length; i += 1) {
        const node = nodes[i];
        if (node.nodeType === 8 /* comment node */ && node.textContent.trim() === text) {
            return i;
        }
    }
    return nodes.length;
}
function claim_html_tag(nodes, is_svg) {
    // find html opening tag
    const start_index = find_comment(nodes, 'HTML_TAG_START', 0);
    const end_index = find_comment(nodes, 'HTML_TAG_END', start_index);
    if (start_index === end_index) {
        return new HtmlTagHydration(undefined, is_svg);
    }
    init_claim_info(nodes);
    const html_tag_nodes = nodes.splice(start_index, end_index - start_index + 1);
    detach(html_tag_nodes[0]);
    detach(html_tag_nodes[html_tag_nodes.length - 1]);
    const claimed_nodes = html_tag_nodes.slice(1, html_tag_nodes.length - 1);
    for (const n of claimed_nodes) {
        n.claim_order = nodes.claim_info.total_claimed;
        nodes.claim_info.total_claimed += 1;
    }
    return new HtmlTagHydration(claimed_nodes, is_svg);
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}
class HtmlTag {
    constructor(is_svg = false) {
        this.is_svg = false;
        this.is_svg = is_svg;
        this.e = this.n = null;
    }
    c(html) {
        this.h(html);
    }
    m(html, target, anchor = null) {
        if (!this.e) {
            if (this.is_svg)
                this.e = svg_element(target.nodeName);
            /** #7364  target for <template> may be provided as #document-fragment(11) */
            else
                this.e = element((target.nodeType === 11 ? 'TEMPLATE' : target.nodeName));
            this.t = target.tagName !== 'TEMPLATE' ? target : target.content;
            this.c(html);
        }
        this.i(anchor);
    }
    h(html) {
        this.e.innerHTML = html;
        this.n = Array.from(this.e.nodeName === 'TEMPLATE' ? this.e.content.childNodes : this.e.childNodes);
    }
    i(anchor) {
        for (let i = 0; i < this.n.length; i += 1) {
            insert(this.t, this.n[i], anchor);
        }
    }
    p(html) {
        this.d();
        this.h(html);
        this.i(this.a);
    }
    d() {
        this.n.forEach(detach);
    }
}
class HtmlTagHydration extends HtmlTag {
    constructor(claimed_nodes, is_svg = false) {
        super(is_svg);
        this.e = this.n = null;
        this.l = claimed_nodes;
    }
    c(html) {
        if (this.l) {
            this.n = this.l;
        }
        else {
            super.c(html);
        }
    }
    i(anchor) {
        for (let i = 0; i < this.n.length; i += 1) {
            insert_hydration(this.t, this.n[i], anchor);
        }
    }
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

const matchIconName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      // Allow provider without '@': "provider:prefix:name"
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIconName(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIconName(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIconName(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIconName = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!((icon.provider === "" || icon.provider.match(matchIconName)) && (allowSimpleName && icon.prefix === "" || icon.prefix.match(matchIconName)) && icon.name.match(matchIconName));
};

const defaultIconDimensions = Object.freeze(
  {
    left: 0,
    top: 0,
    width: 16,
    height: 16
  }
);
const defaultIconTransformations = Object.freeze({
  rotate: 0,
  vFlip: false,
  hFlip: false
});
const defaultIconProps = Object.freeze({
  ...defaultIconDimensions,
  ...defaultIconTransformations
});
const defaultExtendedIconProps = Object.freeze({
  ...defaultIconProps,
  body: "",
  hidden: false
});

function mergeIconTransformations(obj1, obj2) {
  const result = {};
  if (!obj1.hFlip !== !obj2.hFlip) {
    result.hFlip = true;
  }
  if (!obj1.vFlip !== !obj2.vFlip) {
    result.vFlip = true;
  }
  const rotate = ((obj1.rotate || 0) + (obj2.rotate || 0)) % 4;
  if (rotate) {
    result.rotate = rotate;
  }
  return result;
}

function mergeIconData(parent, child) {
  const result = mergeIconTransformations(parent, child);
  for (const key in defaultExtendedIconProps) {
    if (key in defaultIconTransformations) {
      if (key in parent && !(key in result)) {
        result[key] = defaultIconTransformations[key];
      }
    } else if (key in child) {
      result[key] = child[key];
    } else if (key in parent) {
      result[key] = parent[key];
    }
  }
  return result;
}

function getIconsTree(data, names) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  const resolved = /* @__PURE__ */ Object.create(null);
  function resolve(name) {
    if (icons[name]) {
      return resolved[name] = [];
    }
    if (!(name in resolved)) {
      resolved[name] = null;
      const parent = aliases[name] && aliases[name].parent;
      const value = parent && resolve(parent);
      if (value) {
        resolved[name] = [parent].concat(value);
      }
    }
    return resolved[name];
  }
  (names || Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}

function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(
      icons[name2] || aliases[name2],
      currentProps
    );
  }
  parse(name);
  tree.forEach(parse);
  return mergeIconData(data, currentProps);
}

function parseIconSet(data, callback) {
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const tree = getIconsTree(data);
  for (const name in tree) {
    const item = tree[name];
    if (item) {
      callback(name, internalGetIconData(data, name, item));
      names.push(name);
    }
  }
  return names;
}

const optionalPropertyDefaults = {
  provider: "",
  aliases: {},
  not_found: {},
  ...defaultIconDimensions
};
function checkOptionalProps(item, defaults) {
  for (const prop in defaults) {
    if (prop in item && typeof item[prop] !== typeof defaults[prop]) {
      return false;
    }
  }
  return true;
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  if (!checkOptionalProps(obj, optionalPropertyDefaults)) {
    return null;
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(
      icon,
      defaultExtendedIconProps
    )) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(
      icon,
      defaultExtendedIconProps
    )) {
      return null;
    }
  }
  return data;
}

const dataStorage = /* @__PURE__ */ Object.create(null);
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ new Set()
  };
}
function getStorage(provider, prefix) {
  const providerStorage = dataStorage[provider] || (dataStorage[provider] = /* @__PURE__ */ Object.create(null));
  return providerStorage[prefix] || (providerStorage[prefix] = newStorage(provider, prefix));
}
function addIconSet(storage, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage.icons[name] = icon;
    } else {
      storage.missing.add(name);
    }
  });
}
function addIconToStorage(storage, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage.icons[name] = { ...icon };
      return true;
    }
  } catch (err) {
  }
  return false;
}

let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  if (icon) {
    const storage = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage.icons[iconName] || (storage.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage, icon.name, data);
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = data.provider || "";
  }
  if (simpleNames && !provider && !data.prefix) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (icon && addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  const prefix = data.prefix;
  if (!validateIconName({
    provider,
    prefix,
    name: "a"
  })) {
    return false;
  }
  const storage = getStorage(provider, prefix);
  return !!addIconSet(storage, data);
}

const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  // Dimensions
  ...defaultIconSizeCustomisations,
  // Transformations
  ...defaultIconTransformations
});

const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision || 100;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}

function splitSVGDefs(content, tag = "defs") {
  let defs = "";
  const index = content.indexOf("<" + tag);
  while (index >= 0) {
    const start = content.indexOf(">", index);
    const end = content.indexOf("</" + tag);
    if (start === -1 || end === -1) {
      break;
    }
    const endEnd = content.indexOf(">", end);
    if (endEnd === -1) {
      break;
    }
    defs += content.slice(start + 1, end).trim();
    content = content.slice(0, index).trim() + content.slice(endEnd + 1);
  }
  return {
    defs,
    content
  };
}
function mergeDefsAndContent(defs, content) {
  return defs ? "<defs>" + defs + "</defs>" + content : content;
}
function wrapSVGContent(body, start, end) {
  const split = splitSVGDefs(body);
  return mergeDefsAndContent(split.defs, start + split.content + end);
}

const isUnsetKeyword = (value) => value === "unset" || value === "undefined" || value === "none";
function iconToSVG(icon, customisations) {
  const fullIcon = {
    ...defaultIconProps,
    ...icon
  };
  const fullCustomisations = {
    ...defaultIconCustomisations,
    ...customisations
  };
  const box = {
    left: fullIcon.left,
    top: fullIcon.top,
    width: fullIcon.width,
    height: fullIcon.height
  };
  let body = fullIcon.body;
  [fullIcon, fullCustomisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push(
          "translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")"
        );
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push(
        "translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")"
      );
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift(
          "rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")"
        );
        break;
      case 2:
        transformations.unshift(
          "rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")"
        );
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift(
          "rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")"
        );
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== box.top) {
        tempValue = box.left;
        box.left = box.top;
        box.top = tempValue;
      }
      if (box.width !== box.height) {
        tempValue = box.width;
        box.width = box.height;
        box.height = tempValue;
      }
    }
    if (transformations.length) {
      body = wrapSVGContent(
        body,
        '<g transform="' + transformations.join(" ") + '">',
        "</g>"
      );
    }
  });
  const customisationsWidth = fullCustomisations.width;
  const customisationsHeight = fullCustomisations.height;
  const boxWidth = box.width;
  const boxHeight = box.height;
  let width;
  let height;
  if (customisationsWidth === null) {
    height = customisationsHeight === null ? "1em" : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
    width = calculateSize(height, boxWidth / boxHeight);
  } else {
    width = customisationsWidth === "auto" ? boxWidth : customisationsWidth;
    height = customisationsHeight === null ? calculateSize(width, boxHeight / boxWidth) : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
  }
  const attributes = {};
  const setAttr = (prop, value) => {
    if (!isUnsetKeyword(value)) {
      attributes[prop] = value.toString();
    }
  };
  setAttr("width", width);
  setAttr("height", height);
  const viewBox = [box.left, box.top, boxWidth, boxHeight];
  attributes.viewBox = viewBox.join(" ");
  return {
    attributes,
    viewBox,
    body
  };
}

const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  const suffix = "suffix" + (Math.random() * 16777216 | Date.now()).toString(16);
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(
      // Allowed characters before id: [#;"]
      // Allowed characters after id: [)"], .[a-z]
      new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"),
      "$1" + newID + suffix + "$3"
    );
  });
  body = body.replace(new RegExp(suffix, "g"), "");
  return body;
}

const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}

function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    // API hosts
    resources,
    // Root path
    path: source.path || "/",
    // URL length limit
    maxURL: source.maxURL || 500,
    // Timeout before next host is used.
    rotate: source.rotate || 750,
    // Timeout before failing query.
    timeout: source.timeout || 5e3,
    // Randomise default API end point.
    random: source.random === true,
    // Start index
    index: source.index || 0,
    // Receive data after time out (used if time out kicks in first, then API module sends data anyway).
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}

const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
};
let fetchModule = detectFetch();
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = prefix + ".json?icons=";
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  const maxLength = calculateMaxLength(provider, prefix);
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    const config = getAPIConfig(provider);
    if (config) {
      return config.path;
    }
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      const urlParams = new URLSearchParams({
        icons: iconsList
      });
      path += prefix + ".json?" + urlParams.toString();
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        if (data === 404) {
          callback("abort", data);
        } else {
          callback("next", defaultError);
        }
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};

function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const providerStorage = storage[provider] || (storage[provider] = /* @__PURE__ */ Object.create(null));
    const localStorage = providerStorage[prefix] || (providerStorage[prefix] = getStorage(provider, prefix));
    let list;
    if (name in localStorage.icons) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing.has(name)) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}

function removeCallback(storages, id) {
  storages.forEach((storage) => {
    const items = storage.loaderCallbacks;
    if (items) {
      storage.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage) {
  if (!storage.pendingCallbacksFlag) {
    storage.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage.pendingCallbacksFlag = false;
      const items = storage.loaderCallbacks ? storage.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage.provider;
      const prefix = storage.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage.missing.has(name)) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([storage], item.id);
          }
          item.callback(
            icons.loaded.slice(0),
            icons.missing.slice(0),
            icons.pending.slice(0),
            item.abort
          );
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((storage) => {
    (storage.loaderCallbacks || (storage.loaderCallbacks = [])).push(item);
  });
  return abort;
}

function listToIcons(list, validate = true, simpleNames = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}

// src/config.ts
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};

// src/query.ts
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}

// src/index.ts
function initRedundancy(cfg) {
  const config = {
    ...defaultConfig,
    ...cfg
  };
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(
      config,
      payload,
      queryCallback,
      (data, error) => {
        cleanup();
        if (doneCallback) {
          doneCallback(data, error);
        }
      }
    );
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    return queries.find((value) => {
      return callback(value);
    }) || null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}

function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (!redundancyCache[provider]) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send = api.send;
      }
    }
  }
  if (!redundancy || !send) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send, callback)().abort;
}

const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
const browserStorageLimit = 50;

function getStoredItem(func, key) {
  try {
    return func.getItem(key);
  } catch (err) {
  }
}
function setStoredItem(func, key, value) {
  try {
    func.setItem(key, value);
    return true;
  } catch (err) {
  }
}
function removeStoredItem(func, key) {
  try {
    func.removeItem(key);
  } catch (err) {
  }
}

function setBrowserStorageItemsCount(storage, value) {
  return setStoredItem(storage, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage) {
  return parseInt(getStoredItem(storage, browserCacheCountKey)) || 0;
}

const browserStorageConfig = {
  local: true,
  session: true
};
const browserStorageEmptyItems = {
  local: /* @__PURE__ */ new Set(),
  session: /* @__PURE__ */ new Set()
};
let browserStorageStatus = false;
function setBrowserStorageStatus(status) {
  browserStorageStatus = status;
}

let _window = typeof window === "undefined" ? {} : window;
function getBrowserStorage(key) {
  const attr = key + "Storage";
  try {
    if (_window && _window[attr] && typeof _window[attr].length === "number") {
      return _window[attr];
    }
  } catch (err) {
  }
  browserStorageConfig[key] = false;
}

function iterateBrowserStorage(key, callback) {
  const func = getBrowserStorage(key);
  if (!func) {
    return;
  }
  const version = getStoredItem(func, browserCacheVersionKey);
  if (version !== browserCacheVersion) {
    if (version) {
      const total2 = getBrowserStorageItemsCount(func);
      for (let i = 0; i < total2; i++) {
        removeStoredItem(func, browserCachePrefix + i.toString());
      }
    }
    setStoredItem(func, browserCacheVersionKey, browserCacheVersion);
    setBrowserStorageItemsCount(func, 0);
    return;
  }
  const minTime = Math.floor(Date.now() / browserStorageHour) - browserStorageCacheExpiration;
  const parseItem = (index) => {
    const name = browserCachePrefix + index.toString();
    const item = getStoredItem(func, name);
    if (typeof item !== "string") {
      return;
    }
    try {
      const data = JSON.parse(item);
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && // Valid item: run callback
      callback(data, index)) {
        return true;
      }
    } catch (err) {
    }
    removeStoredItem(func, name);
  };
  let total = getBrowserStorageItemsCount(func);
  for (let i = total - 1; i >= 0; i--) {
    if (!parseItem(i)) {
      if (i === total - 1) {
        total--;
        setBrowserStorageItemsCount(func, total);
      } else {
        browserStorageEmptyItems[key].add(i);
      }
    }
  }
}

function initBrowserStorage() {
  if (browserStorageStatus) {
    return;
  }
  setBrowserStorageStatus(true);
  for (const key in browserStorageConfig) {
    iterateBrowserStorage(key, (item) => {
      const iconSet = item.data;
      const provider = item.provider;
      const prefix = iconSet.prefix;
      const storage = getStorage(
        provider,
        prefix
      );
      if (!addIconSet(storage, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage.lastModifiedCached = storage.lastModifiedCached ? Math.min(storage.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}

function updateLastModified(storage, lastModified) {
  const lastValue = storage.lastModifiedCached;
  if (
    // Matches or newer
    lastValue && lastValue >= lastModified
  ) {
    return lastValue === lastModified;
  }
  storage.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage.provider || iconSet.prefix !== storage.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage, data) {
  if (!browserStorageStatus) {
    initBrowserStorage();
  }
  function store(key) {
    let func;
    if (!browserStorageConfig[key] || !(func = getBrowserStorage(key))) {
      return;
    }
    const set = browserStorageEmptyItems[key];
    let index;
    if (set.size) {
      set.delete(index = Array.from(set).shift());
    } else {
      index = getBrowserStorageItemsCount(func);
      if (index >= browserStorageLimit || !setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage.provider,
      data
    };
    return setStoredItem(
      func,
      browserCachePrefix + index.toString(),
      JSON.stringify(item)
    );
  }
  if (data.lastModified && !updateLastModified(storage, data.lastModified)) {
    return;
  }
  if (!Object.keys(data.icons).length) {
    return;
  }
  if (data.not_found) {
    data = Object.assign({}, data);
    delete data.not_found;
  }
  if (!store("local")) {
    store("session");
  }
}

function emptyCallback() {
}
function loadedNewIcons(storage) {
  if (!storage.iconsLoaderFlag) {
    storage.iconsLoaderFlag = true;
    setTimeout(() => {
      storage.iconsLoaderFlag = false;
      updateCallbacks(storage);
    });
  }
}
function loadNewIcons(storage, icons) {
  if (!storage.iconsToLoad) {
    storage.iconsToLoad = icons;
  } else {
    storage.iconsToLoad = storage.iconsToLoad.concat(icons).sort();
  }
  if (!storage.iconsQueueFlag) {
    storage.iconsQueueFlag = true;
    setTimeout(() => {
      storage.iconsQueueFlag = false;
      const { provider, prefix } = storage;
      const icons2 = storage.iconsToLoad;
      delete storage.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(
                storage,
                data
              );
              if (!parsed.length) {
                return;
              }
              const pending = storage.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(
            sortedIcons.loaded,
            sortedIcons.missing,
            sortedIcons.pending,
            emptyCallback
          );
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const { provider, prefix } = icon;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push(getStorage(provider, prefix));
    const providerNewIcons = newIcons[provider] || (newIcons[provider] = /* @__PURE__ */ Object.create(null));
    if (!providerNewIcons[prefix]) {
      providerNewIcons[prefix] = [];
    }
  });
  sortedIcons.pending.forEach((icon) => {
    const { provider, prefix, name } = icon;
    const storage = getStorage(provider, prefix);
    const pendingQueue = storage.pendingIcons || (storage.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage) => {
    const { provider, prefix } = storage;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage, newIcons[provider][prefix]);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};

function mergeCustomisations(defaults, item) {
  const result = {
    ...defaults
  };
  for (const key in item) {
    const value = item[key];
    const valueType = typeof value;
    if (key in defaultIconSizeCustomisations) {
      if (value === null || value && (valueType === "string" || valueType === "number")) {
        result[key] = value;
      }
    } else if (valueType === typeof result[key]) {
      result[key] = key === "rotate" ? value % 4 : value;
    }
  }
  return result;
}

const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}

function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
        split = 90;
    }
    if (split) {
      let num = parseFloat(value.slice(0, value.length - units.length));
      if (isNaN(num)) {
        return 0;
      }
      num = num / split;
      return num % 1 === 0 ? cleanup(num) : 0;
    }
  }
  return defaultValue;
}

function iconToHTML(body, attributes) {
  let renderAttribsHTML = body.indexOf("xlink:") === -1 ? "" : ' xmlns:xlink="http://www.w3.org/1999/xlink"';
  for (const attr in attributes) {
    renderAttribsHTML += " " + attr + '="' + attributes[attr] + '"';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg"' + renderAttribsHTML + ">" + body + "</svg>";
}

function encodeSVGforURL(svg) {
  return svg.replace(/"/g, "'").replace(/%/g, "%25").replace(/#/g, "%23").replace(/</g, "%3C").replace(/>/g, "%3E").replace(/\s+/g, " ");
}
function svgToData(svg) {
  return "data:image/svg+xml," + encodeSVGforURL(svg);
}
function svgToURL(svg) {
  return 'url("' + svgToData(svg) + '")';
}

const defaultExtendedIconCustomisations = {
    ...defaultIconCustomisations,
    inline: false,
};

/**
 * Default SVG attributes
 */
const svgDefaults = {
    'xmlns': 'http://www.w3.org/2000/svg',
    'xmlns:xlink': 'http://www.w3.org/1999/xlink',
    'aria-hidden': true,
    'role': 'img',
};
/**
 * Style modes
 */
const commonProps = {
    display: 'inline-block',
};
const monotoneProps = {
    'background-color': 'currentColor',
};
const coloredProps = {
    'background-color': 'transparent',
};
// Dynamically add common props to variables above
const propsToAdd = {
    image: 'var(--svg)',
    repeat: 'no-repeat',
    size: '100% 100%',
};
const propsToAddTo = {
    '-webkit-mask': monotoneProps,
    'mask': monotoneProps,
    'background': coloredProps,
};
for (const prefix in propsToAddTo) {
    const list = propsToAddTo[prefix];
    for (const prop in propsToAdd) {
        list[prefix + '-' + prop] = propsToAdd[prop];
    }
}
/**
 * Fix size: add 'px' to numbers
 */
function fixSize(value) {
    return value + (value.match(/^[-0-9.]+$/) ? 'px' : '');
}
/**
 * Generate icon from properties
 */
function render(
// Icon must be validated before calling this function
icon, 
// Properties
props) {
    const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
    // Check mode
    const mode = props.mode || 'svg';
    const componentProps = (mode === 'svg' ? { ...svgDefaults } : {});
    if (icon.body.indexOf('xlink:') === -1) {
        delete componentProps['xmlns:xlink'];
    }
    // Create style if missing
    let style = typeof props.style === 'string' ? props.style : '';
    // Get element properties
    for (let key in props) {
        const value = props[key];
        if (value === void 0) {
            continue;
        }
        switch (key) {
            // Properties to ignore
            case 'icon':
            case 'style':
            case 'onLoad':
            case 'mode':
                break;
            // Boolean attributes
            case 'inline':
            case 'hFlip':
            case 'vFlip':
                customisations[key] =
                    value === true || value === 'true' || value === 1;
                break;
            // Flip as string: 'horizontal,vertical'
            case 'flip':
                if (typeof value === 'string') {
                    flipFromString(customisations, value);
                }
                break;
            // Color: copy to style, add extra ';' in case style is missing it
            case 'color':
                style =
                    style +
                        (style.length > 0 && style.trim().slice(-1) !== ';'
                            ? ';'
                            : '') +
                        'color: ' +
                        value +
                        '; ';
                break;
            // Rotation as string
            case 'rotate':
                if (typeof value === 'string') {
                    customisations[key] = rotateFromString(value);
                }
                else if (typeof value === 'number') {
                    customisations[key] = value;
                }
                break;
            // Remove aria-hidden
            case 'ariaHidden':
            case 'aria-hidden':
                if (value !== true && value !== 'true') {
                    delete componentProps['aria-hidden'];
                }
                break;
            default:
                if (key.slice(0, 3) === 'on:') {
                    // Svelte event
                    break;
                }
                // Copy missing property if it does not exist in customisations
                if (defaultExtendedIconCustomisations[key] === void 0) {
                    componentProps[key] = value;
                }
        }
    }
    // Generate icon
    const item = iconToSVG(icon, customisations);
    const renderAttribs = item.attributes;
    // Inline display
    if (customisations.inline) {
        // Style overrides it
        style = 'vertical-align: -0.125em; ' + style;
    }
    if (mode === 'svg') {
        // Add icon stuff
        Object.assign(componentProps, renderAttribs);
        // Style
        if (style !== '') {
            componentProps.style = style;
        }
        // Counter for ids based on "id" property to render icons consistently on server and client
        let localCounter = 0;
        let id = props.id;
        if (typeof id === 'string') {
            // Convert '-' to '_' to avoid errors in animations
            id = id.replace(/-/g, '_');
        }
        // Generate HTML
        return {
            svg: true,
            attributes: componentProps,
            body: replaceIDs(item.body, id ? () => id + 'ID' + localCounter++ : 'iconifySvelte'),
        };
    }
    // Render <span> with style
    const { body, width, height } = icon;
    const useMask = mode === 'mask' ||
        (mode === 'bg' ? false : body.indexOf('currentColor') !== -1);
    // Generate SVG
    const html = iconToHTML(body, {
        ...renderAttribs,
        width: width + '',
        height: height + '',
    });
    // Generate style
    const url = svgToURL(html);
    const styles = {
        '--svg': url,
    };
    const size = (prop) => {
        const value = renderAttribs[prop];
        if (value) {
            styles[prop] = fixSize(value);
        }
    };
    size('width');
    size('height');
    Object.assign(styles, commonProps, useMask ? monotoneProps : coloredProps);
    let customStyle = '';
    for (const key in styles) {
        customStyle += key + ': ' + styles[key] + ';';
    }
    componentProps.style = customStyle + style;
    return {
        svg: false,
        attributes: componentProps,
    };
}
/**
 * Initialise stuff
 */
// Enable short names
allowSimpleNames(true);
// Set API module
setAPIModule('', fetchAPIModule);
/**
 * Browser stuff
 */
if (typeof document !== 'undefined' && typeof window !== 'undefined') {
    // Set cache and load existing cache
    initBrowserStorage();
    const _window = window;
    // Load icons from global "IconifyPreload"
    if (_window.IconifyPreload !== void 0) {
        const preload = _window.IconifyPreload;
        const err = 'Invalid IconifyPreload syntax.';
        if (typeof preload === 'object' && preload !== null) {
            (preload instanceof Array ? preload : [preload]).forEach((item) => {
                try {
                    if (
                    // Check if item is an object and not null/array
                    typeof item !== 'object' ||
                        item === null ||
                        item instanceof Array ||
                        // Check for 'icons' and 'prefix'
                        typeof item.icons !== 'object' ||
                        typeof item.prefix !== 'string' ||
                        // Add icon set
                        !addCollection(item)) {
                        console.error(err);
                    }
                }
                catch (e) {
                    console.error(err);
                }
            });
        }
    }
    // Set API from global "IconifyProviders"
    if (_window.IconifyProviders !== void 0) {
        const providers = _window.IconifyProviders;
        if (typeof providers === 'object' && providers !== null) {
            for (let key in providers) {
                const err = 'IconifyProviders[' + key + '] is invalid.';
                try {
                    const value = providers[key];
                    if (typeof value !== 'object' ||
                        !value ||
                        value.resources === void 0) {
                        continue;
                    }
                    if (!addAPIProvider(key, value)) {
                        console.error(err);
                    }
                }
                catch (e) {
                    console.error(err);
                }
            }
        }
    }
}
/**
 * Check if component needs to be updated
 */
function checkIconState(icon, state, mounted, callback, onload) {
    // Abort loading icon
    function abortLoading() {
        if (state.loading) {
            state.loading.abort();
            state.loading = null;
        }
    }
    // Icon is an object
    if (typeof icon === 'object' &&
        icon !== null &&
        typeof icon.body === 'string') {
        // Stop loading
        state.name = '';
        abortLoading();
        return { data: { ...defaultIconProps, ...icon } };
    }
    // Invalid icon?
    let iconName;
    if (typeof icon !== 'string' ||
        (iconName = stringToIcon(icon, false, true)) === null) {
        abortLoading();
        return null;
    }
    // Load icon
    const data = getIconData(iconName);
    if (!data) {
        // Icon data is not available
        // Do not load icon until component is mounted
        if (mounted && (!state.loading || state.loading.name !== icon)) {
            // New icon to load
            abortLoading();
            state.name = '';
            state.loading = {
                name: icon,
                abort: loadIcons([iconName], callback),
            };
        }
        return null;
    }
    // Icon data is available
    abortLoading();
    if (state.name !== icon) {
        state.name = icon;
        if (onload && !state.destroyed) {
            onload(icon);
        }
    }
    // Add classes
    const classes = ['iconify'];
    if (iconName.prefix !== '') {
        classes.push('iconify--' + iconName.prefix);
    }
    if (iconName.provider !== '') {
        classes.push('iconify--' + iconName.provider);
    }
    return { data, classes };
}
/**
 * Generate icon
 */
function generateIcon(icon, props) {
    return icon
        ? render({
            ...defaultIconProps,
            ...icon,
        }, props)
        : null;
}

/* generated by Svelte v3.59.1 */

function create_if_block$1(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1$1;
		return create_else_block$1;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (115:1) {:else}
function create_else_block$1(ctx) {
	let span;
	let span_levels = [/*data*/ ctx[0].attributes];
	let span_data = {};

	for (let i = 0; i < span_levels.length; i += 1) {
		span_data = assign(span_data, span_levels[i]);
	}

	return {
		c() {
			span = element("span");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			children(span).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(span, span_data);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
		},
		p(ctx, dirty) {
			set_attributes(span, span_data = get_spread_update(span_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (111:1) {#if data.svg}
function create_if_block_1$1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$1(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] && create_if_block$1(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*data*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$1(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		{
			const iconData = checkIconState($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

let Component$1 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
};

const exports = {}; const module = { exports };

!function(e,t){"object"==typeof exports&&"undefined"!=typeof module?module.exports=t():"function"==typeof define&&define.amd?define(t):(e="undefined"!=typeof globalThis?globalThis:e||self).axios=t();}(undefined,(function(){function e(e,t){var n=Object.keys(e);if(Object.getOwnPropertySymbols){var r=Object.getOwnPropertySymbols(e);t&&(r=r.filter((function(t){return Object.getOwnPropertyDescriptor(e,t).enumerable}))),n.push.apply(n,r);}return n}function t(t){for(var n=1;n<arguments.length;n++){var r=null!=arguments[n]?arguments[n]:{};n%2?e(Object(r),!0).forEach((function(e){a(t,e,r[e]);})):Object.getOwnPropertyDescriptors?Object.defineProperties(t,Object.getOwnPropertyDescriptors(r)):e(Object(r)).forEach((function(e){Object.defineProperty(t,e,Object.getOwnPropertyDescriptor(r,e));}));}return t}function n(e){return n="function"==typeof Symbol&&"symbol"==typeof Symbol.iterator?function(e){return typeof e}:function(e){return e&&"function"==typeof Symbol&&e.constructor===Symbol&&e!==Symbol.prototype?"symbol":typeof e},n(e)}function r(e,t){if(!(e instanceof t))throw new TypeError("Cannot call a class as a function")}function o(e,t){for(var n=0;n<t.length;n++){var r=t[n];r.enumerable=r.enumerable||!1,r.configurable=!0,"value"in r&&(r.writable=!0),Object.defineProperty(e,r.key,r);}}function i(e,t,n){return t&&o(e.prototype,t),n&&o(e,n),Object.defineProperty(e,"prototype",{writable:!1}),e}function a(e,t,n){return t in e?Object.defineProperty(e,t,{value:n,enumerable:!0,configurable:!0,writable:!0}):e[t]=n,e}function s(e,t){return c(e)||function(e,t){var n=null==e?null:"undefined"!=typeof Symbol&&e[Symbol.iterator]||e["@@iterator"];if(null==n)return;var r,o,i=[],a=!0,s=!1;try{for(n=n.call(e);!(a=(r=n.next()).done)&&(i.push(r.value),!t||i.length!==t);a=!0);}catch(e){s=!0,o=e;}finally{try{a||null==n.return||n.return();}finally{if(s)throw o}}return i}(e,t)||l(e,t)||p()}function u(e){return function(e){if(Array.isArray(e))return d(e)}(e)||f(e)||l(e)||function(){throw new TypeError("Invalid attempt to spread non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method.")}()}function c(e){if(Array.isArray(e))return e}function f(e){if("undefined"!=typeof Symbol&&null!=e[Symbol.iterator]||null!=e["@@iterator"])return Array.from(e)}function l(e,t){if(e){if("string"==typeof e)return d(e,t);var n=Object.prototype.toString.call(e).slice(8,-1);return "Object"===n&&e.constructor&&(n=e.constructor.name),"Map"===n||"Set"===n?Array.from(e):"Arguments"===n||/^(?:Ui|I)nt(?:8|16|32)(?:Clamped)?Array$/.test(n)?d(e,t):void 0}}function d(e,t){(null==t||t>e.length)&&(t=e.length);for(var n=0,r=new Array(t);n<t;n++)r[n]=e[n];return r}function p(){throw new TypeError("Invalid attempt to destructure non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method.")}function h(e,t){return function(){return e.apply(t,arguments)}}var m,y=Object.prototype.toString,v=Object.getPrototypeOf,b=(m=Object.create(null),function(e){var t=y.call(e);return m[t]||(m[t]=t.slice(8,-1).toLowerCase())}),g=function(e){return e=e.toLowerCase(),function(t){return b(t)===e}},w=function(e){return function(t){return n(t)===e}},O=Array.isArray,E=w("undefined");var S=g("ArrayBuffer");var R=w("string"),A=w("function"),j=w("number"),T=function(e){return null!==e&&"object"===n(e)},P=function(e){if("object"!==b(e))return !1;var t=v(e);return !(null!==t&&t!==Object.prototype&&null!==Object.getPrototypeOf(t)||Symbol.toStringTag in e||Symbol.iterator in e)},N=g("Date"),x=g("File"),C=g("Blob"),k=g("FileList"),_=g("URLSearchParams");function F(e,t){var r,o,i=arguments.length>2&&void 0!==arguments[2]?arguments[2]:{},a=i.allOwnKeys,s=void 0!==a&&a;if(null!=e)if("object"!==n(e)&&(e=[e]),O(e))for(r=0,o=e.length;r<o;r++)t.call(null,e[r],r,e);else {var u,c=s?Object.getOwnPropertyNames(e):Object.keys(e),f=c.length;for(r=0;r<f;r++)u=c[r],t.call(null,e[u],u,e);}}function U(e,t){t=t.toLowerCase();for(var n,r=Object.keys(e),o=r.length;o-- >0;)if(t===(n=r[o]).toLowerCase())return n;return null}var D="undefined"!=typeof globalThis?globalThis:"undefined"!=typeof self?self:"undefined"!=typeof window?window:global,B=function(e){return !E(e)&&e!==D};var L,I=(L="undefined"!=typeof Uint8Array&&v(Uint8Array),function(e){return L&&e instanceof L}),q=g("HTMLFormElement"),z=function(e){var t=Object.prototype.hasOwnProperty;return function(e,n){return t.call(e,n)}}(),M=g("RegExp"),H=function(e,t){var n=Object.getOwnPropertyDescriptors(e),r={};F(n,(function(n,o){var i;!1!==(i=t(n,o,e))&&(r[o]=i||n);})),Object.defineProperties(e,r);},J="abcdefghijklmnopqrstuvwxyz",W="0123456789",K={DIGIT:W,ALPHA:J,ALPHA_DIGIT:J+J.toUpperCase()+W};var V=g("AsyncFunction"),G={isArray:O,isArrayBuffer:S,isBuffer:function(e){return null!==e&&!E(e)&&null!==e.constructor&&!E(e.constructor)&&A(e.constructor.isBuffer)&&e.constructor.isBuffer(e)},isFormData:function(e){var t;return e&&("function"==typeof FormData&&e instanceof FormData||A(e.append)&&("formdata"===(t=b(e))||"object"===t&&A(e.toString)&&"[object FormData]"===e.toString()))},isArrayBufferView:function(e){return "undefined"!=typeof ArrayBuffer&&ArrayBuffer.isView?ArrayBuffer.isView(e):e&&e.buffer&&S(e.buffer)},isString:R,isNumber:j,isBoolean:function(e){return !0===e||!1===e},isObject:T,isPlainObject:P,isUndefined:E,isDate:N,isFile:x,isBlob:C,isRegExp:M,isFunction:A,isStream:function(e){return T(e)&&A(e.pipe)},isURLSearchParams:_,isTypedArray:I,isFileList:k,forEach:F,merge:function e(){for(var t=B(this)&&this||{},n=t.caseless,r={},o=function(t,o){var i=n&&U(r,o)||o;P(r[i])&&P(t)?r[i]=e(r[i],t):P(t)?r[i]=e({},t):O(t)?r[i]=t.slice():r[i]=t;},i=0,a=arguments.length;i<a;i++)arguments[i]&&F(arguments[i],o);return r},extend:function(e,t,n){var r=arguments.length>3&&void 0!==arguments[3]?arguments[3]:{},o=r.allOwnKeys;return F(t,(function(t,r){n&&A(t)?e[r]=h(t,n):e[r]=t;}),{allOwnKeys:o}),e},trim:function(e){return e.trim?e.trim():e.replace(/^[\s\uFEFF\xA0]+|[\s\uFEFF\xA0]+$/g,"")},stripBOM:function(e){return 65279===e.charCodeAt(0)&&(e=e.slice(1)),e},inherits:function(e,t,n,r){e.prototype=Object.create(t.prototype,r),e.prototype.constructor=e,Object.defineProperty(e,"super",{value:t.prototype}),n&&Object.assign(e.prototype,n);},toFlatObject:function(e,t,n,r){var o,i,a,s={};if(t=t||{},null==e)return t;do{for(i=(o=Object.getOwnPropertyNames(e)).length;i-- >0;)a=o[i],r&&!r(a,e,t)||s[a]||(t[a]=e[a],s[a]=!0);e=!1!==n&&v(e);}while(e&&(!n||n(e,t))&&e!==Object.prototype);return t},kindOf:b,kindOfTest:g,endsWith:function(e,t,n){e=String(e),(void 0===n||n>e.length)&&(n=e.length),n-=t.length;var r=e.indexOf(t,n);return -1!==r&&r===n},toArray:function(e){if(!e)return null;if(O(e))return e;var t=e.length;if(!j(t))return null;for(var n=new Array(t);t-- >0;)n[t]=e[t];return n},forEachEntry:function(e,t){for(var n,r=(e&&e[Symbol.iterator]).call(e);(n=r.next())&&!n.done;){var o=n.value;t.call(e,o[0],o[1]);}},matchAll:function(e,t){for(var n,r=[];null!==(n=e.exec(t));)r.push(n);return r},isHTMLForm:q,hasOwnProperty:z,hasOwnProp:z,reduceDescriptors:H,freezeMethods:function(e){H(e,(function(t,n){if(A(e)&&-1!==["arguments","caller","callee"].indexOf(n))return !1;var r=e[n];A(r)&&(t.enumerable=!1,"writable"in t?t.writable=!1:t.set||(t.set=function(){throw Error("Can not rewrite read-only method '"+n+"'")}));}));},toObjectSet:function(e,t){var n={},r=function(e){e.forEach((function(e){n[e]=!0;}));};return O(e)?r(e):r(String(e).split(t)),n},toCamelCase:function(e){return e.toLowerCase().replace(/[-_\s]([a-z\d])(\w*)/g,(function(e,t,n){return t.toUpperCase()+n}))},noop:function(){},toFiniteNumber:function(e,t){return e=+e,Number.isFinite(e)?e:t},findKey:U,global:D,isContextDefined:B,ALPHABET:K,generateString:function(){for(var e=arguments.length>0&&void 0!==arguments[0]?arguments[0]:16,t=arguments.length>1&&void 0!==arguments[1]?arguments[1]:K.ALPHA_DIGIT,n="",r=t.length;e--;)n+=t[Math.random()*r|0];return n},isSpecCompliantForm:function(e){return !!(e&&A(e.append)&&"FormData"===e[Symbol.toStringTag]&&e[Symbol.iterator])},toJSONObject:function(e){var t=new Array(10);return function e(n,r){if(T(n)){if(t.indexOf(n)>=0)return;if(!("toJSON"in n)){t[r]=n;var o=O(n)?[]:{};return F(n,(function(t,n){var i=e(t,r+1);!E(i)&&(o[n]=i);})),t[r]=void 0,o}}return n}(e,0)},isAsyncFn:V,isThenable:function(e){return e&&(T(e)||A(e))&&A(e.then)&&A(e.catch)}};function X(e,t,n,r,o){Error.call(this),Error.captureStackTrace?Error.captureStackTrace(this,this.constructor):this.stack=(new Error).stack,this.message=e,this.name="AxiosError",t&&(this.code=t),n&&(this.config=n),r&&(this.request=r),o&&(this.response=o);}G.inherits(X,Error,{toJSON:function(){return {message:this.message,name:this.name,description:this.description,number:this.number,fileName:this.fileName,lineNumber:this.lineNumber,columnNumber:this.columnNumber,stack:this.stack,config:G.toJSONObject(this.config),code:this.code,status:this.response&&this.response.status?this.response.status:null}}});var $=X.prototype,Q={};["ERR_BAD_OPTION_VALUE","ERR_BAD_OPTION","ECONNABORTED","ETIMEDOUT","ERR_NETWORK","ERR_FR_TOO_MANY_REDIRECTS","ERR_DEPRECATED","ERR_BAD_RESPONSE","ERR_BAD_REQUEST","ERR_CANCELED","ERR_NOT_SUPPORT","ERR_INVALID_URL"].forEach((function(e){Q[e]={value:e};})),Object.defineProperties(X,Q),Object.defineProperty($,"isAxiosError",{value:!0}),X.from=function(e,t,n,r,o,i){var a=Object.create($);return G.toFlatObject(e,a,(function(e){return e!==Error.prototype}),(function(e){return "isAxiosError"!==e})),X.call(a,e.message,t,n,r,o),a.cause=e,a.name=e.name,i&&Object.assign(a,i),a};function Z(e){return G.isPlainObject(e)||G.isArray(e)}function Y(e){return G.endsWith(e,"[]")?e.slice(0,-2):e}function ee(e,t,n){return e?e.concat(t).map((function(e,t){return e=Y(e),!n&&t?"["+e+"]":e})).join(n?".":""):t}var te=G.toFlatObject(G,{},null,(function(e){return /^is[A-Z]/.test(e)}));function ne(e,t,r){if(!G.isObject(e))throw new TypeError("target must be an object");t=t||new FormData;var o=(r=G.toFlatObject(r,{metaTokens:!0,dots:!1,indexes:!1},!1,(function(e,t){return !G.isUndefined(t[e])}))).metaTokens,i=r.visitor||f,a=r.dots,s=r.indexes,u=(r.Blob||"undefined"!=typeof Blob&&Blob)&&G.isSpecCompliantForm(t);if(!G.isFunction(i))throw new TypeError("visitor must be a function");function c(e){if(null===e)return "";if(G.isDate(e))return e.toISOString();if(!u&&G.isBlob(e))throw new X("Blob is not supported. Use a Buffer instead.");return G.isArrayBuffer(e)||G.isTypedArray(e)?u&&"function"==typeof Blob?new Blob([e]):Buffer.from(e):e}function f(e,r,i){var u=e;if(e&&!i&&"object"===n(e))if(G.endsWith(r,"{}"))r=o?r:r.slice(0,-2),e=JSON.stringify(e);else if(G.isArray(e)&&function(e){return G.isArray(e)&&!e.some(Z)}(e)||(G.isFileList(e)||G.endsWith(r,"[]"))&&(u=G.toArray(e)))return r=Y(r),u.forEach((function(e,n){!G.isUndefined(e)&&null!==e&&t.append(!0===s?ee([r],n,a):null===s?r:r+"[]",c(e));})),!1;return !!Z(e)||(t.append(ee(i,r,a),c(e)),!1)}var l=[],d=Object.assign(te,{defaultVisitor:f,convertValue:c,isVisitable:Z});if(!G.isObject(e))throw new TypeError("data must be an object");return function e(n,r){if(!G.isUndefined(n)){if(-1!==l.indexOf(n))throw Error("Circular reference detected in "+r.join("."));l.push(n),G.forEach(n,(function(n,o){!0===(!(G.isUndefined(n)||null===n)&&i.call(t,n,G.isString(o)?o.trim():o,r,d))&&e(n,r?r.concat(o):[o]);})),l.pop();}}(e),t}function re(e){var t={"!":"%21","'":"%27","(":"%28",")":"%29","~":"%7E","%20":"+","%00":"\0"};return encodeURIComponent(e).replace(/[!'()~]|%20|%00/g,(function(e){return t[e]}))}function oe(e,t){this._pairs=[],e&&ne(e,this,t);}var ie=oe.prototype;function ae(e){return encodeURIComponent(e).replace(/%3A/gi,":").replace(/%24/g,"$").replace(/%2C/gi,",").replace(/%20/g,"+").replace(/%5B/gi,"[").replace(/%5D/gi,"]")}function se(e,t,n){if(!t)return e;var r,o=n&&n.encode||ae,i=n&&n.serialize;if(r=i?i(t,n):G.isURLSearchParams(t)?t.toString():new oe(t,n).toString(o)){var a=e.indexOf("#");-1!==a&&(e=e.slice(0,a)),e+=(-1===e.indexOf("?")?"?":"&")+r;}return e}ie.append=function(e,t){this._pairs.push([e,t]);},ie.toString=function(e){var t=e?function(t){return e.call(this,t,re)}:re;return this._pairs.map((function(e){return t(e[0])+"="+t(e[1])}),"").join("&")};var ue,ce=function(){function e(){r(this,e),this.handlers=[];}return i(e,[{key:"use",value:function(e,t,n){return this.handlers.push({fulfilled:e,rejected:t,synchronous:!!n&&n.synchronous,runWhen:n?n.runWhen:null}),this.handlers.length-1}},{key:"eject",value:function(e){this.handlers[e]&&(this.handlers[e]=null);}},{key:"clear",value:function(){this.handlers&&(this.handlers=[]);}},{key:"forEach",value:function(e){G.forEach(this.handlers,(function(t){null!==t&&e(t);}));}}]),e}(),fe={silentJSONParsing:!0,forcedJSONParsing:!0,clarifyTimeoutError:!1},le={isBrowser:!0,classes:{URLSearchParams:"undefined"!=typeof URLSearchParams?URLSearchParams:oe,FormData:"undefined"!=typeof FormData?FormData:null,Blob:"undefined"!=typeof Blob?Blob:null},protocols:["http","https","file","blob","url","data"]},de="undefined"!=typeof window&&"undefined"!=typeof document,pe=(ue="undefined"!=typeof navigator&&navigator.product,de&&["ReactNative","NativeScript","NS"].indexOf(ue)<0),he="undefined"!=typeof WorkerGlobalScope&&self instanceof WorkerGlobalScope&&"function"==typeof self.importScripts,me=t(t({},Object.freeze({__proto__:null,hasBrowserEnv:de,hasStandardBrowserWebWorkerEnv:he,hasStandardBrowserEnv:pe})),le);function ye(e){function t(e,n,r,o){var i=e[o++],a=Number.isFinite(+i),s=o>=e.length;return i=!i&&G.isArray(r)?r.length:i,s?(G.hasOwnProp(r,i)?r[i]=[r[i],n]:r[i]=n,!a):(r[i]&&G.isObject(r[i])||(r[i]=[]),t(e,n,r[i],o)&&G.isArray(r[i])&&(r[i]=function(e){var t,n,r={},o=Object.keys(e),i=o.length;for(t=0;t<i;t++)r[n=o[t]]=e[n];return r}(r[i])),!a)}if(G.isFormData(e)&&G.isFunction(e.entries)){var n={};return G.forEachEntry(e,(function(e,r){t(function(e){return G.matchAll(/\w+|\[(\w*)]/g,e).map((function(e){return "[]"===e[0]?"":e[1]||e[0]}))}(e),r,n,0);})),n}return null}var ve={transitional:fe,adapter:["xhr","http"],transformRequest:[function(e,t){var n,r=t.getContentType()||"",o=r.indexOf("application/json")>-1,i=G.isObject(e);if(i&&G.isHTMLForm(e)&&(e=new FormData(e)),G.isFormData(e))return o&&o?JSON.stringify(ye(e)):e;if(G.isArrayBuffer(e)||G.isBuffer(e)||G.isStream(e)||G.isFile(e)||G.isBlob(e))return e;if(G.isArrayBufferView(e))return e.buffer;if(G.isURLSearchParams(e))return t.setContentType("application/x-www-form-urlencoded;charset=utf-8",!1),e.toString();if(i){if(r.indexOf("application/x-www-form-urlencoded")>-1)return function(e,t){return ne(e,new me.classes.URLSearchParams,Object.assign({visitor:function(e,t,n,r){return me.isNode&&G.isBuffer(e)?(this.append(t,e.toString("base64")),!1):r.defaultVisitor.apply(this,arguments)}},t))}(e,this.formSerializer).toString();if((n=G.isFileList(e))||r.indexOf("multipart/form-data")>-1){var a=this.env&&this.env.FormData;return ne(n?{"files[]":e}:e,a&&new a,this.formSerializer)}}return i||o?(t.setContentType("application/json",!1),function(e,t,n){if(G.isString(e))try{return (t||JSON.parse)(e),G.trim(e)}catch(e){if("SyntaxError"!==e.name)throw e}return (n||JSON.stringify)(e)}(e)):e}],transformResponse:[function(e){var t=this.transitional||ve.transitional,n=t&&t.forcedJSONParsing,r="json"===this.responseType;if(e&&G.isString(e)&&(n&&!this.responseType||r)){var o=!(t&&t.silentJSONParsing)&&r;try{return JSON.parse(e)}catch(e){if(o){if("SyntaxError"===e.name)throw X.from(e,X.ERR_BAD_RESPONSE,this,null,this.response);throw e}}}return e}],timeout:0,xsrfCookieName:"XSRF-TOKEN",xsrfHeaderName:"X-XSRF-TOKEN",maxContentLength:-1,maxBodyLength:-1,env:{FormData:me.classes.FormData,Blob:me.classes.Blob},validateStatus:function(e){return e>=200&&e<300},headers:{common:{Accept:"application/json, text/plain, */*","Content-Type":void 0}}};G.forEach(["delete","get","head","post","put","patch"],(function(e){ve.headers[e]={};}));var be=ve,ge=G.toObjectSet(["age","authorization","content-length","content-type","etag","expires","from","host","if-modified-since","if-unmodified-since","last-modified","location","max-forwards","proxy-authorization","referer","retry-after","user-agent"]),we=Symbol("internals");function Oe(e){return e&&String(e).trim().toLowerCase()}function Ee(e){return !1===e||null==e?e:G.isArray(e)?e.map(Ee):String(e)}function Se(e,t,n,r,o){return G.isFunction(r)?r.call(this,t,n):(o&&(t=n),G.isString(t)?G.isString(r)?-1!==t.indexOf(r):G.isRegExp(r)?r.test(t):void 0:void 0)}var Re=function(e,t){function n(e){r(this,n),e&&this.set(e);}return i(n,[{key:"set",value:function(e,t,n){var r=this;function o(e,t,n){var o=Oe(t);if(!o)throw new Error("header name must be a non-empty string");var i=G.findKey(r,o);(!i||void 0===r[i]||!0===n||void 0===n&&!1!==r[i])&&(r[i||t]=Ee(e));}var i,a,s,u,c,f=function(e,t){return G.forEach(e,(function(e,n){return o(e,n,t)}))};return G.isPlainObject(e)||e instanceof this.constructor?f(e,t):G.isString(e)&&(e=e.trim())&&!/^[-_a-zA-Z0-9^`|~,!#$%&'*+.]+$/.test(e.trim())?f((c={},(i=e)&&i.split("\n").forEach((function(e){u=e.indexOf(":"),a=e.substring(0,u).trim().toLowerCase(),s=e.substring(u+1).trim(),!a||c[a]&&ge[a]||("set-cookie"===a?c[a]?c[a].push(s):c[a]=[s]:c[a]=c[a]?c[a]+", "+s:s);})),c),t):null!=e&&o(t,e,n),this}},{key:"get",value:function(e,t){if(e=Oe(e)){var n=G.findKey(this,e);if(n){var r=this[n];if(!t)return r;if(!0===t)return function(e){for(var t,n=Object.create(null),r=/([^\s,;=]+)\s*(?:=\s*([^,;]+))?/g;t=r.exec(e);)n[t[1]]=t[2];return n}(r);if(G.isFunction(t))return t.call(this,r,n);if(G.isRegExp(t))return t.exec(r);throw new TypeError("parser must be boolean|regexp|function")}}}},{key:"has",value:function(e,t){if(e=Oe(e)){var n=G.findKey(this,e);return !(!n||void 0===this[n]||t&&!Se(0,this[n],n,t))}return !1}},{key:"delete",value:function(e,t){var n=this,r=!1;function o(e){if(e=Oe(e)){var o=G.findKey(n,e);!o||t&&!Se(0,n[o],o,t)||(delete n[o],r=!0);}}return G.isArray(e)?e.forEach(o):o(e),r}},{key:"clear",value:function(e){for(var t=Object.keys(this),n=t.length,r=!1;n--;){var o=t[n];e&&!Se(0,this[o],o,e,!0)||(delete this[o],r=!0);}return r}},{key:"normalize",value:function(e){var t=this,n={};return G.forEach(this,(function(r,o){var i=G.findKey(n,o);if(i)return t[i]=Ee(r),void delete t[o];var a=e?function(e){return e.trim().toLowerCase().replace(/([a-z\d])(\w*)/g,(function(e,t,n){return t.toUpperCase()+n}))}(o):String(o).trim();a!==o&&delete t[o],t[a]=Ee(r),n[a]=!0;})),this}},{key:"concat",value:function(){for(var e,t=arguments.length,n=new Array(t),r=0;r<t;r++)n[r]=arguments[r];return (e=this.constructor).concat.apply(e,[this].concat(n))}},{key:"toJSON",value:function(e){var t=Object.create(null);return G.forEach(this,(function(n,r){null!=n&&!1!==n&&(t[r]=e&&G.isArray(n)?n.join(", "):n);})),t}},{key:Symbol.iterator,value:function(){return Object.entries(this.toJSON())[Symbol.iterator]()}},{key:"toString",value:function(){return Object.entries(this.toJSON()).map((function(e){var t=s(e,2);return t[0]+": "+t[1]})).join("\n")}},{key:Symbol.toStringTag,get:function(){return "AxiosHeaders"}}],[{key:"from",value:function(e){return e instanceof this?e:new this(e)}},{key:"concat",value:function(e){for(var t=new this(e),n=arguments.length,r=new Array(n>1?n-1:0),o=1;o<n;o++)r[o-1]=arguments[o];return r.forEach((function(e){return t.set(e)})),t}},{key:"accessor",value:function(e){var t=(this[we]=this[we]={accessors:{}}).accessors,n=this.prototype;function r(e){var r=Oe(e);t[r]||(!function(e,t){var n=G.toCamelCase(" "+t);["get","set","has"].forEach((function(r){Object.defineProperty(e,r+n,{value:function(e,n,o){return this[r].call(this,t,e,n,o)},configurable:!0});}));}(n,e),t[r]=!0);}return G.isArray(e)?e.forEach(r):r(e),this}}]),n}();Re.accessor(["Content-Type","Content-Length","Accept","Accept-Encoding","User-Agent","Authorization"]),G.reduceDescriptors(Re.prototype,(function(e,t){var n=e.value,r=t[0].toUpperCase()+t.slice(1);return {get:function(){return n},set:function(e){this[r]=e;}}})),G.freezeMethods(Re);var Ae=Re;function je(e,t){var n=this||be,r=t||n,o=Ae.from(r.headers),i=r.data;return G.forEach(e,(function(e){i=e.call(n,i,o.normalize(),t?t.status:void 0);})),o.normalize(),i}function Te(e){return !(!e||!e.__CANCEL__)}function Pe(e,t,n){X.call(this,null==e?"canceled":e,X.ERR_CANCELED,t,n),this.name="CanceledError";}G.inherits(Pe,X,{__CANCEL__:!0});var Ne=me.hasStandardBrowserEnv?{write:function(e,t,n,r,o,i){var a=[e+"="+encodeURIComponent(t)];G.isNumber(n)&&a.push("expires="+new Date(n).toGMTString()),G.isString(r)&&a.push("path="+r),G.isString(o)&&a.push("domain="+o),!0===i&&a.push("secure"),document.cookie=a.join("; ");},read:function(e){var t=document.cookie.match(new RegExp("(^|;\\s*)("+e+")=([^;]*)"));return t?decodeURIComponent(t[3]):null},remove:function(e){this.write(e,"",Date.now()-864e5);}}:{write:function(){},read:function(){return null},remove:function(){}};function xe(e,t){return e&&!/^([a-z][a-z\d+\-.]*:)?\/\//i.test(t)?function(e,t){return t?e.replace(/\/+$/,"")+"/"+t.replace(/^\/+/,""):e}(e,t):t}var Ce=me.hasStandardBrowserEnv?function(){var e,t=/(msie|trident)/i.test(navigator.userAgent),n=document.createElement("a");function r(e){var r=e;return t&&(n.setAttribute("href",r),r=n.href),n.setAttribute("href",r),{href:n.href,protocol:n.protocol?n.protocol.replace(/:$/,""):"",host:n.host,search:n.search?n.search.replace(/^\?/,""):"",hash:n.hash?n.hash.replace(/^#/,""):"",hostname:n.hostname,port:n.port,pathname:"/"===n.pathname.charAt(0)?n.pathname:"/"+n.pathname}}return e=r(window.location.href),function(t){var n=G.isString(t)?r(t):t;return n.protocol===e.protocol&&n.host===e.host}}():function(){return !0};function ke(e,t){var n=0,r=function(e,t){e=e||10;var n,r=new Array(e),o=new Array(e),i=0,a=0;return t=void 0!==t?t:1e3,function(s){var u=Date.now(),c=o[a];n||(n=u),r[i]=s,o[i]=u;for(var f=a,l=0;f!==i;)l+=r[f++],f%=e;if((i=(i+1)%e)===a&&(a=(a+1)%e),!(u-n<t)){var d=c&&u-c;return d?Math.round(1e3*l/d):void 0}}}(50,250);return function(o){var i=o.loaded,a=o.lengthComputable?o.total:void 0,s=i-n,u=r(s);n=i;var c={loaded:i,total:a,progress:a?i/a:void 0,bytes:s,rate:u||void 0,estimated:u&&a&&i<=a?(a-i)/u:void 0,event:o};c[t?"download":"upload"]=!0,e(c);}}var _e={http:null,xhr:"undefined"!=typeof XMLHttpRequest&&function(e){return new Promise((function(t,n){var r,o,i,a=e.data,s=Ae.from(e.headers).normalize(),d=e.responseType,h=e.withXSRFToken;function m(){e.cancelToken&&e.cancelToken.unsubscribe(r),e.signal&&e.signal.removeEventListener("abort",r);}if(G.isFormData(a))if(me.hasStandardBrowserEnv||me.hasStandardBrowserWebWorkerEnv)s.setContentType(!1);else if(!1!==(o=s.getContentType())){var y=o?o.split(";").map((function(e){return e.trim()})).filter(Boolean):[],v=c(i=y)||f(i)||l(i)||p(),b=v[0],g=v.slice(1);s.setContentType([b||"multipart/form-data"].concat(u(g)).join("; "));}var w=new XMLHttpRequest;if(e.auth){var O=e.auth.username||"",E=e.auth.password?unescape(encodeURIComponent(e.auth.password)):"";s.set("Authorization","Basic "+btoa(O+":"+E));}var S=xe(e.baseURL,e.url);function R(){if(w){var r=Ae.from("getAllResponseHeaders"in w&&w.getAllResponseHeaders());!function(e,t,n){var r=n.config.validateStatus;n.status&&r&&!r(n.status)?t(new X("Request failed with status code "+n.status,[X.ERR_BAD_REQUEST,X.ERR_BAD_RESPONSE][Math.floor(n.status/100)-4],n.config,n.request,n)):e(n);}((function(e){t(e),m();}),(function(e){n(e),m();}),{data:d&&"text"!==d&&"json"!==d?w.response:w.responseText,status:w.status,statusText:w.statusText,headers:r,config:e,request:w}),w=null;}}if(w.open(e.method.toUpperCase(),se(S,e.params,e.paramsSerializer),!0),w.timeout=e.timeout,"onloadend"in w?w.onloadend=R:w.onreadystatechange=function(){w&&4===w.readyState&&(0!==w.status||w.responseURL&&0===w.responseURL.indexOf("file:"))&&setTimeout(R);},w.onabort=function(){w&&(n(new X("Request aborted",X.ECONNABORTED,e,w)),w=null);},w.onerror=function(){n(new X("Network Error",X.ERR_NETWORK,e,w)),w=null;},w.ontimeout=function(){var t=e.timeout?"timeout of "+e.timeout+"ms exceeded":"timeout exceeded",r=e.transitional||fe;e.timeoutErrorMessage&&(t=e.timeoutErrorMessage),n(new X(t,r.clarifyTimeoutError?X.ETIMEDOUT:X.ECONNABORTED,e,w)),w=null;},me.hasStandardBrowserEnv&&(h&&G.isFunction(h)&&(h=h(e)),h||!1!==h&&Ce(S))){var A=e.xsrfHeaderName&&e.xsrfCookieName&&Ne.read(e.xsrfCookieName);A&&s.set(e.xsrfHeaderName,A);}void 0===a&&s.setContentType(null),"setRequestHeader"in w&&G.forEach(s.toJSON(),(function(e,t){w.setRequestHeader(t,e);})),G.isUndefined(e.withCredentials)||(w.withCredentials=!!e.withCredentials),d&&"json"!==d&&(w.responseType=e.responseType),"function"==typeof e.onDownloadProgress&&w.addEventListener("progress",ke(e.onDownloadProgress,!0)),"function"==typeof e.onUploadProgress&&w.upload&&w.upload.addEventListener("progress",ke(e.onUploadProgress)),(e.cancelToken||e.signal)&&(r=function(t){w&&(n(!t||t.type?new Pe(null,e,w):t),w.abort(),w=null);},e.cancelToken&&e.cancelToken.subscribe(r),e.signal&&(e.signal.aborted?r():e.signal.addEventListener("abort",r)));var j,T=(j=/^([-+\w]{1,25})(:?\/\/|:)/.exec(S))&&j[1]||"";T&&-1===me.protocols.indexOf(T)?n(new X("Unsupported protocol "+T+":",X.ERR_BAD_REQUEST,e)):w.send(a||null);}))}};G.forEach(_e,(function(e,t){if(e){try{Object.defineProperty(e,"name",{value:t});}catch(e){}Object.defineProperty(e,"adapterName",{value:t});}}));var Fe=function(e){return "- ".concat(e)},Ue=function(e){return G.isFunction(e)||null===e||!1===e},De=function(e){for(var t,n,r=(e=G.isArray(e)?e:[e]).length,o={},i=0;i<r;i++){var a=void 0;if(n=t=e[i],!Ue(t)&&void 0===(n=_e[(a=String(t)).toLowerCase()]))throw new X("Unknown adapter '".concat(a,"'"));if(n)break;o[a||"#"+i]=n;}if(!n){var u=Object.entries(o).map((function(e){var t=s(e,2),n=t[0],r=t[1];return "adapter ".concat(n," ")+(!1===r?"is not supported by the environment":"is not available in the build")}));throw new X("There is no suitable adapter to dispatch the request "+(r?u.length>1?"since :\n"+u.map(Fe).join("\n"):" "+Fe(u[0]):"as no adapter specified"),"ERR_NOT_SUPPORT")}return n};function Be(e){if(e.cancelToken&&e.cancelToken.throwIfRequested(),e.signal&&e.signal.aborted)throw new Pe(null,e)}function Le(e){return Be(e),e.headers=Ae.from(e.headers),e.data=je.call(e,e.transformRequest),-1!==["post","put","patch"].indexOf(e.method)&&e.headers.setContentType("application/x-www-form-urlencoded",!1),De(e.adapter||be.adapter)(e).then((function(t){return Be(e),t.data=je.call(e,e.transformResponse,t),t.headers=Ae.from(t.headers),t}),(function(t){return Te(t)||(Be(e),t&&t.response&&(t.response.data=je.call(e,e.transformResponse,t.response),t.response.headers=Ae.from(t.response.headers))),Promise.reject(t)}))}var Ie=function(e){return e instanceof Ae?e.toJSON():e};function qe(e,t){t=t||{};var n={};function r(e,t,n){return G.isPlainObject(e)&&G.isPlainObject(t)?G.merge.call({caseless:n},e,t):G.isPlainObject(t)?G.merge({},t):G.isArray(t)?t.slice():t}function o(e,t,n){return G.isUndefined(t)?G.isUndefined(e)?void 0:r(void 0,e,n):r(e,t,n)}function i(e,t){if(!G.isUndefined(t))return r(void 0,t)}function a(e,t){return G.isUndefined(t)?G.isUndefined(e)?void 0:r(void 0,e):r(void 0,t)}function s(n,o,i){return i in t?r(n,o):i in e?r(void 0,n):void 0}var u={url:i,method:i,data:i,baseURL:a,transformRequest:a,transformResponse:a,paramsSerializer:a,timeout:a,timeoutMessage:a,withCredentials:a,withXSRFToken:a,adapter:a,responseType:a,xsrfCookieName:a,xsrfHeaderName:a,onUploadProgress:a,onDownloadProgress:a,decompress:a,maxContentLength:a,maxBodyLength:a,beforeRedirect:a,transport:a,httpAgent:a,httpsAgent:a,cancelToken:a,socketPath:a,responseEncoding:a,validateStatus:s,headers:function(e,t){return o(Ie(e),Ie(t),!0)}};return G.forEach(Object.keys(Object.assign({},e,t)),(function(r){var i=u[r]||o,a=i(e[r],t[r],r);G.isUndefined(a)&&i!==s||(n[r]=a);})),n}var ze="1.6.2",Me={};["object","boolean","number","function","string","symbol"].forEach((function(e,t){Me[e]=function(r){return n(r)===e||"a"+(t<1?"n ":" ")+e};}));var He={};Me.transitional=function(e,t,n){function r(e,t){return "[Axios v1.6.2] Transitional option '"+e+"'"+t+(n?". "+n:"")}return function(n,o,i){if(!1===e)throw new X(r(o," has been removed"+(t?" in "+t:"")),X.ERR_DEPRECATED);return t&&!He[o]&&(He[o]=!0,console.warn(r(o," has been deprecated since v"+t+" and will be removed in the near future"))),!e||e(n,o,i)}};var Je={assertOptions:function(e,t,r){if("object"!==n(e))throw new X("options must be an object",X.ERR_BAD_OPTION_VALUE);for(var o=Object.keys(e),i=o.length;i-- >0;){var a=o[i],s=t[a];if(s){var u=e[a],c=void 0===u||s(u,a,e);if(!0!==c)throw new X("option "+a+" must be "+c,X.ERR_BAD_OPTION_VALUE)}else if(!0!==r)throw new X("Unknown option "+a,X.ERR_BAD_OPTION)}},validators:Me},We=Je.validators,Ke=function(){function e(t){r(this,e),this.defaults=t,this.interceptors={request:new ce,response:new ce};}return i(e,[{key:"request",value:function(e,t){"string"==typeof e?(t=t||{}).url=e:t=e||{};var n=t=qe(this.defaults,t),r=n.transitional,o=n.paramsSerializer,i=n.headers;void 0!==r&&Je.assertOptions(r,{silentJSONParsing:We.transitional(We.boolean),forcedJSONParsing:We.transitional(We.boolean),clarifyTimeoutError:We.transitional(We.boolean)},!1),null!=o&&(G.isFunction(o)?t.paramsSerializer={serialize:o}:Je.assertOptions(o,{encode:We.function,serialize:We.function},!0)),t.method=(t.method||this.defaults.method||"get").toLowerCase();var a=i&&G.merge(i.common,i[t.method]);i&&G.forEach(["delete","get","head","post","put","patch","common"],(function(e){delete i[e];})),t.headers=Ae.concat(a,i);var s=[],u=!0;this.interceptors.request.forEach((function(e){"function"==typeof e.runWhen&&!1===e.runWhen(t)||(u=u&&e.synchronous,s.unshift(e.fulfilled,e.rejected));}));var c,f=[];this.interceptors.response.forEach((function(e){f.push(e.fulfilled,e.rejected);}));var l,d=0;if(!u){var p=[Le.bind(this),void 0];for(p.unshift.apply(p,s),p.push.apply(p,f),l=p.length,c=Promise.resolve(t);d<l;)c=c.then(p[d++],p[d++]);return c}l=s.length;var h=t;for(d=0;d<l;){var m=s[d++],y=s[d++];try{h=m(h);}catch(e){y.call(this,e);break}}try{c=Le.call(this,h);}catch(e){return Promise.reject(e)}for(d=0,l=f.length;d<l;)c=c.then(f[d++],f[d++]);return c}},{key:"getUri",value:function(e){return se(xe((e=qe(this.defaults,e)).baseURL,e.url),e.params,e.paramsSerializer)}}]),e}();G.forEach(["delete","get","head","options"],(function(e){Ke.prototype[e]=function(t,n){return this.request(qe(n||{},{method:e,url:t,data:(n||{}).data}))};})),G.forEach(["post","put","patch"],(function(e){function t(t){return function(n,r,o){return this.request(qe(o||{},{method:e,headers:t?{"Content-Type":"multipart/form-data"}:{},url:n,data:r}))}}Ke.prototype[e]=t(),Ke.prototype[e+"Form"]=t(!0);}));var Ve=Ke,Ge=function(){function e(t){if(r(this,e),"function"!=typeof t)throw new TypeError("executor must be a function.");var n;this.promise=new Promise((function(e){n=e;}));var o=this;this.promise.then((function(e){if(o._listeners){for(var t=o._listeners.length;t-- >0;)o._listeners[t](e);o._listeners=null;}})),this.promise.then=function(e){var t,n=new Promise((function(e){o.subscribe(e),t=e;})).then(e);return n.cancel=function(){o.unsubscribe(t);},n},t((function(e,t,r){o.reason||(o.reason=new Pe(e,t,r),n(o.reason));}));}return i(e,[{key:"throwIfRequested",value:function(){if(this.reason)throw this.reason}},{key:"subscribe",value:function(e){this.reason?e(this.reason):this._listeners?this._listeners.push(e):this._listeners=[e];}},{key:"unsubscribe",value:function(e){if(this._listeners){var t=this._listeners.indexOf(e);-1!==t&&this._listeners.splice(t,1);}}}],[{key:"source",value:function(){var t;return {token:new e((function(e){t=e;})),cancel:t}}}]),e}();var Xe={Continue:100,SwitchingProtocols:101,Processing:102,EarlyHints:103,Ok:200,Created:201,Accepted:202,NonAuthoritativeInformation:203,NoContent:204,ResetContent:205,PartialContent:206,MultiStatus:207,AlreadyReported:208,ImUsed:226,MultipleChoices:300,MovedPermanently:301,Found:302,SeeOther:303,NotModified:304,UseProxy:305,Unused:306,TemporaryRedirect:307,PermanentRedirect:308,BadRequest:400,Unauthorized:401,PaymentRequired:402,Forbidden:403,NotFound:404,MethodNotAllowed:405,NotAcceptable:406,ProxyAuthenticationRequired:407,RequestTimeout:408,Conflict:409,Gone:410,LengthRequired:411,PreconditionFailed:412,PayloadTooLarge:413,UriTooLong:414,UnsupportedMediaType:415,RangeNotSatisfiable:416,ExpectationFailed:417,ImATeapot:418,MisdirectedRequest:421,UnprocessableEntity:422,Locked:423,FailedDependency:424,TooEarly:425,UpgradeRequired:426,PreconditionRequired:428,TooManyRequests:429,RequestHeaderFieldsTooLarge:431,UnavailableForLegalReasons:451,InternalServerError:500,NotImplemented:501,BadGateway:502,ServiceUnavailable:503,GatewayTimeout:504,HttpVersionNotSupported:505,VariantAlsoNegotiates:506,InsufficientStorage:507,LoopDetected:508,NotExtended:510,NetworkAuthenticationRequired:511};Object.entries(Xe).forEach((function(e){var t=s(e,2),n=t[0],r=t[1];Xe[r]=n;}));var $e=Xe;var Qe=function e(t){var n=new Ve(t),r=h(Ve.prototype.request,n);return G.extend(r,Ve.prototype,n,{allOwnKeys:!0}),G.extend(r,n,null,{allOwnKeys:!0}),r.create=function(n){return e(qe(t,n))},r}(be);return Qe.Axios=Ve,Qe.CanceledError=Pe,Qe.CancelToken=Ge,Qe.isCancel=Te,Qe.VERSION=ze,Qe.toFormData=ne,Qe.AxiosError=X,Qe.Cancel=Qe.CanceledError,Qe.all=function(e){return Promise.all(e)},Qe.spread=function(e){return function(t){return e.apply(null,t)}},Qe.isAxiosError=function(e){return G.isObject(e)&&!0===e.isAxiosError},Qe.mergeConfig=qe,Qe.AxiosHeaders=Ae,Qe.formToJSON=function(e){return ye(G.isHTMLForm(e)?new FormData(e):e)},Qe.getAdapter=De,Qe.HttpStatusCode=$e,Qe.default=Qe,Qe}));





var axios = module.exports;

/* generated by Svelte v3.59.1 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[15] = list[i].label;
	child_ctx[16] = list[i].type;
	child_ctx[17] = list[i].placeholder;
	child_ctx[18] = list[i].required;
	child_ctx[21] = i;
	const constants_0 = `${/*label*/ child_ctx[15]}-${/*i*/ child_ctx[21]}`;
	child_ctx[19] = constants_0;
	return child_ctx;
}

// (249:18) 
function create_if_block_7(ctx) {
	let div;
	let html_tag;
	let raw_value = /*submission_confirmation*/ ctx[4].error + "";
	let t0;
	let button;
	let icon;
	let t1;
	let span;
	let t2_value = /*submission_confirmation*/ ctx[4].submit_again + "";
	let t2;
	let current;
	let mounted;
	let dispose;
	icon = new Component$1({ props: { icon: "mdi:arrow-left-thin" } });

	return {
		c() {
			div = element("div");
			html_tag = new HtmlTagHydration(false);
			t0 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			t1 = space();
			span = element("span");
			t2 = text(t2_value);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			html_tag = claim_html_tag(div_nodes, false);
			t0 = claim_space(div_nodes);
			button = claim_element(div_nodes, "BUTTON", { class: true });
			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			t1 = claim_space(button_nodes);
			span = claim_element(button_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t2 = claim_text(span_nodes, t2_value);
			span_nodes.forEach(detach);
			button_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			html_tag.a = t0;
			attr(span, "class", "svelte-o7fd5j");
			attr(button, "class", "svelte-o7fd5j");
			attr(div, "class", "section-container content svelte-o7fd5j");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			html_tag.m(raw_value, div);
			append_hydration(div, t0);
			append_hydration(div, button);
			mount_component(icon, button, null);
			append_hydration(button, t1);
			append_hydration(button, span);
			append_hydration(span, t2);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[14]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if ((!current || dirty & /*submission_confirmation*/ 16) && raw_value !== (raw_value = /*submission_confirmation*/ ctx[4].error + "")) html_tag.p(raw_value);
			if ((!current || dirty & /*submission_confirmation*/ 16) && t2_value !== (t2_value = /*submission_confirmation*/ ctx[4].submit_again + "")) set_data(t2, t2_value);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div);
			destroy_component(icon);
			mounted = false;
			dispose();
		}
	};
}

// (241:22) 
function create_if_block_6(ctx) {
	let div;
	let html_tag;
	let raw_value = /*submission_confirmation*/ ctx[4].content + "";
	let t0;
	let button;
	let icon;
	let t1;
	let span;
	let t2_value = /*submission_confirmation*/ ctx[4].submit_again + "";
	let t2;
	let current;
	let mounted;
	let dispose;
	icon = new Component$1({ props: { icon: "mdi:arrow-left-thin" } });

	return {
		c() {
			div = element("div");
			html_tag = new HtmlTagHydration(false);
			t0 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			t1 = space();
			span = element("span");
			t2 = text(t2_value);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			html_tag = claim_html_tag(div_nodes, false);
			t0 = claim_space(div_nodes);
			button = claim_element(div_nodes, "BUTTON", { class: true });
			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			t1 = claim_space(button_nodes);
			span = claim_element(button_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t2 = claim_text(span_nodes, t2_value);
			span_nodes.forEach(detach);
			button_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			html_tag.a = t0;
			attr(span, "class", "svelte-o7fd5j");
			attr(button, "class", "svelte-o7fd5j");
			attr(div, "class", "section-container content svelte-o7fd5j");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			html_tag.m(raw_value, div);
			append_hydration(div, t0);
			append_hydration(div, button);
			mount_component(icon, button, null);
			append_hydration(button, t1);
			append_hydration(button, span);
			append_hydration(span, t2);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[13]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if ((!current || dirty & /*submission_confirmation*/ 16) && raw_value !== (raw_value = /*submission_confirmation*/ ctx[4].content + "")) html_tag.p(raw_value);
			if ((!current || dirty & /*submission_confirmation*/ 16) && t2_value !== (t2_value = /*submission_confirmation*/ ctx[4].submit_again + "")) set_data(t2, t2_value);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div);
			destroy_component(icon);
			mounted = false;
			dispose();
		}
	};
}

// (186:2) {#if !submitted && !error}
function create_if_block(ctx) {
	let div2;
	let div1;
	let h2;
	let t0;
	let t1;
	let form;
	let t2;
	let div0;
	let raw_value = /*footer_text*/ ctx[3].html + "";
	let t3;
	let button;
	let icon;
	let t4;
	let span;
	let t5_value = /*submit*/ ctx[1].label + "";
	let t5;
	let current;
	let mounted;
	let dispose;
	let each_value = /*fields*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	icon = new Component$1({ props: { icon: /*submit*/ ctx[1].icon } });

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[2]);
			t1 = space();
			form = element("form");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t2 = space();
			div0 = element("div");
			t3 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			t4 = space();
			span = element("span");
			t5 = text(t5_value);
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h2 = claim_element(div1_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[2]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div1_nodes);
			form = claim_element(div1_nodes, "FORM", { class: true });
			var form_nodes = children(form);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(form_nodes);
			}

			t2 = claim_space(form_nodes);
			div0 = claim_element(form_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t3 = claim_space(form_nodes);
			button = claim_element(form_nodes, "BUTTON", { type: true, class: true });
			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			t4 = claim_space(button_nodes);
			span = claim_element(button_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t5 = claim_text(span_nodes, t5_value);
			span_nodes.forEach(detach);
			button_nodes.forEach(detach);
			form_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-o7fd5j");
			attr(div0, "class", "footer-text svelte-o7fd5j");
			attr(span, "class", "svelte-o7fd5j");
			attr(button, "type", "submit");
			attr(button, "class", "button svelte-o7fd5j");
			attr(form, "class", "svelte-o7fd5j");
			attr(div1, "class", "form svelte-o7fd5j");
			attr(div2, "class", "section-container svelte-o7fd5j");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, h2);
			append_hydration(h2, t0);
			append_hydration(div1, t1);
			append_hydration(div1, form);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(form, null);
				}
			}

			append_hydration(form, t2);
			append_hydration(form, div0);
			div0.innerHTML = raw_value;
			append_hydration(form, t3);
			append_hydration(form, button);
			mount_component(icon, button, null);
			append_hydration(button, t4);
			append_hydration(button, span);
			append_hydration(span, t5);
			current = true;

			if (!mounted) {
				dispose = listen(form, "submit", prevent_default(/*submit_form*/ ctx[9]));
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (!current || dirty & /*heading*/ 4) set_data(t0, /*heading*/ ctx[2]);

			if (dirty & /*fields, add_file, files*/ 289) {
				each_value = /*fields*/ ctx[0];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(form, t2);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}

			if ((!current || dirty & /*footer_text*/ 8) && raw_value !== (raw_value = /*footer_text*/ ctx[3].html + "")) div0.innerHTML = raw_value;			const icon_changes = {};
			if (dirty & /*submit*/ 2) icon_changes.icon = /*submit*/ ctx[1].icon;
			icon.$set(icon_changes);
			if ((!current || dirty & /*submit*/ 2) && t5_value !== (t5_value = /*submit*/ ctx[1].label + "")) set_data(t5, t5_value);
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div2);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			mounted = false;
			dispose();
		}
	};
}

// (221:10) {:else}
function create_else_block(ctx) {
	let label;
	let span;
	let t0_value = /*label*/ ctx[15] + "";
	let t0;
	let t1;
	let t2;
	let input;
	let input_name_value;
	let input_placeholder_value;
	let if_block = /*required*/ ctx[18] && create_if_block_5();

	return {
		c() {
			label = element("label");
			span = element("span");
			t0 = text(t0_value);
			t1 = space();
			if (if_block) if_block.c();
			t2 = space();
			input = element("input");
			this.h();
		},
		l(nodes) {
			label = claim_element(nodes, "LABEL", { class: true });
			var label_nodes = children(label);
			span = claim_element(label_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, t0_value);
			t1 = claim_space(span_nodes);
			if (if_block) if_block.l(span_nodes);
			span_nodes.forEach(detach);
			t2 = claim_space(label_nodes);

			input = claim_element(label_nodes, "INPUT", {
				type: true,
				name: true,
				placeholder: true,
				class: true
			});

			label_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "svelte-o7fd5j");
			attr(input, "type", "text");
			attr(input, "name", input_name_value = /*label*/ ctx[15]);
			attr(input, "placeholder", input_placeholder_value = /*placeholder*/ ctx[17]);
			attr(input, "class", "svelte-o7fd5j");
			attr(label, "class", "svelte-o7fd5j");
		},
		m(target, anchor) {
			insert_hydration(target, label, anchor);
			append_hydration(label, span);
			append_hydration(span, t0);
			append_hydration(span, t1);
			if (if_block) if_block.m(span, null);
			append_hydration(label, t2);
			append_hydration(label, input);
		},
		p(ctx, dirty) {
			if (dirty & /*fields*/ 1 && t0_value !== (t0_value = /*label*/ ctx[15] + "")) set_data(t0, t0_value);

			if (/*required*/ ctx[18]) {
				if (if_block) ; else {
					if_block = create_if_block_5();
					if_block.c();
					if_block.m(span, null);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}

			if (dirty & /*fields*/ 1 && input_name_value !== (input_name_value = /*label*/ ctx[15])) {
				attr(input, "name", input_name_value);
			}

			if (dirty & /*fields*/ 1 && input_placeholder_value !== (input_placeholder_value = /*placeholder*/ ctx[17])) {
				attr(input, "placeholder", input_placeholder_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(label);
			if (if_block) if_block.d();
		}
	};
}

// (212:40) 
function create_if_block_3(ctx) {
	let label;
	let span;
	let t0_value = /*label*/ ctx[15] + "";
	let t0;
	let t1;
	let t2;
	let textarea;
	let textarea_name_value;
	let textarea_placeholder_value;
	let if_block = /*required*/ ctx[18] && create_if_block_4();

	return {
		c() {
			label = element("label");
			span = element("span");
			t0 = text(t0_value);
			t1 = space();
			if (if_block) if_block.c();
			t2 = space();
			textarea = element("textarea");
			this.h();
		},
		l(nodes) {
			label = claim_element(nodes, "LABEL", { class: true });
			var label_nodes = children(label);
			span = claim_element(label_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, t0_value);
			t1 = claim_space(span_nodes);
			if (if_block) if_block.l(span_nodes);
			span_nodes.forEach(detach);
			t2 = claim_space(label_nodes);

			textarea = claim_element(label_nodes, "TEXTAREA", {
				name: true,
				placeholder: true,
				class: true
			});

			children(textarea).forEach(detach);
			label_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "svelte-o7fd5j");
			attr(textarea, "name", textarea_name_value = /*label*/ ctx[15]);
			attr(textarea, "placeholder", textarea_placeholder_value = /*placeholder*/ ctx[17]);
			attr(textarea, "class", "svelte-o7fd5j");
			attr(label, "class", "has-textarea svelte-o7fd5j");
		},
		m(target, anchor) {
			insert_hydration(target, label, anchor);
			append_hydration(label, span);
			append_hydration(span, t0);
			append_hydration(span, t1);
			if (if_block) if_block.m(span, null);
			append_hydration(label, t2);
			append_hydration(label, textarea);
		},
		p(ctx, dirty) {
			if (dirty & /*fields*/ 1 && t0_value !== (t0_value = /*label*/ ctx[15] + "")) set_data(t0, t0_value);

			if (/*required*/ ctx[18]) {
				if (if_block) ; else {
					if_block = create_if_block_4();
					if_block.c();
					if_block.m(span, null);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}

			if (dirty & /*fields*/ 1 && textarea_name_value !== (textarea_name_value = /*label*/ ctx[15])) {
				attr(textarea, "name", textarea_name_value);
			}

			if (dirty & /*fields*/ 1 && textarea_placeholder_value !== (textarea_placeholder_value = /*placeholder*/ ctx[17])) {
				attr(textarea, "placeholder", textarea_placeholder_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(label);
			if (if_block) if_block.d();
		}
	};
}

// (193:10) {#if type === "file"}
function create_if_block_1(ctx) {
	let label;
	let span0;
	let t0_value = /*label*/ ctx[15] + "";
	let t0;
	let t1;
	let t2;
	let div;
	let span1;
	let t3_value = (/*files*/ ctx[5][/*id*/ ctx[19]] || "Choose file") + "";
	let t3;
	let t4;
	let span2;
	let t5;
	let icon;
	let t6;
	let input;
	let input_name_value;
	let current;
	let mounted;
	let dispose;
	let if_block = /*required*/ ctx[18] && create_if_block_2();
	icon = new Component$1({ props: { icon: "ep:upload-filled" } });

	function change_handler(...args) {
		return /*change_handler*/ ctx[12](/*id*/ ctx[19], ...args);
	}

	return {
		c() {
			label = element("label");
			span0 = element("span");
			t0 = text(t0_value);
			t1 = space();
			if (if_block) if_block.c();
			t2 = space();
			div = element("div");
			span1 = element("span");
			t3 = text(t3_value);
			t4 = space();
			span2 = element("span");
			t5 = text("Choose\n                  ");
			create_component(icon.$$.fragment);
			t6 = space();
			input = element("input");
			this.h();
		},
		l(nodes) {
			label = claim_element(nodes, "LABEL", { class: true });
			var label_nodes = children(label);
			span0 = claim_element(label_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t0 = claim_text(span0_nodes, t0_value);
			t1 = claim_space(span0_nodes);
			if (if_block) if_block.l(span0_nodes);
			span0_nodes.forEach(detach);
			t2 = claim_space(label_nodes);
			div = claim_element(label_nodes, "DIV", { class: true });
			var div_nodes = children(div);
			span1 = claim_element(div_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t3 = claim_text(span1_nodes, t3_value);
			span1_nodes.forEach(detach);
			t4 = claim_space(div_nodes);
			span2 = claim_element(div_nodes, "SPAN", { class: true });
			var span2_nodes = children(span2);
			t5 = claim_text(span2_nodes, "Choose\n                  ");
			claim_component(icon.$$.fragment, span2_nodes);
			span2_nodes.forEach(detach);
			div_nodes.forEach(detach);
			t6 = claim_space(label_nodes);
			input = claim_element(label_nodes, "INPUT", { name: true, type: true, class: true });
			label_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "svelte-o7fd5j");
			attr(span1, "class", "button-left svelte-o7fd5j");
			attr(span2, "class", "button-right svelte-o7fd5j");
			attr(div, "class", "field-item svelte-o7fd5j");
			attr(input, "name", input_name_value = /*label*/ ctx[15]);
			attr(input, "type", "file");
			attr(input, "class", "svelte-o7fd5j");
			attr(label, "class", "file svelte-o7fd5j");
		},
		m(target, anchor) {
			insert_hydration(target, label, anchor);
			append_hydration(label, span0);
			append_hydration(span0, t0);
			append_hydration(span0, t1);
			if (if_block) if_block.m(span0, null);
			append_hydration(label, t2);
			append_hydration(label, div);
			append_hydration(div, span1);
			append_hydration(span1, t3);
			append_hydration(div, t4);
			append_hydration(div, span2);
			append_hydration(span2, t5);
			mount_component(icon, span2, null);
			append_hydration(label, t6);
			append_hydration(label, input);
			current = true;

			if (!mounted) {
				dispose = listen(input, "change", change_handler);
				mounted = true;
			}
		},
		p(new_ctx, dirty) {
			ctx = new_ctx;
			if ((!current || dirty & /*fields*/ 1) && t0_value !== (t0_value = /*label*/ ctx[15] + "")) set_data(t0, t0_value);

			if (/*required*/ ctx[18]) {
				if (if_block) ; else {
					if_block = create_if_block_2();
					if_block.c();
					if_block.m(span0, null);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}

			if ((!current || dirty & /*files, fields*/ 33) && t3_value !== (t3_value = (/*files*/ ctx[5][/*id*/ ctx[19]] || "Choose file") + "")) set_data(t3, t3_value);

			if (!current || dirty & /*fields*/ 1 && input_name_value !== (input_name_value = /*label*/ ctx[15])) {
				attr(input, "name", input_name_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(label);
			if (if_block) if_block.d();
			destroy_component(icon);
			mounted = false;
			dispose();
		}
	};
}

// (225:16) {#if required}
function create_if_block_5(ctx) {
	let span;
	let t;

	return {
		c() {
			span = element("span");
			t = text("*");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t = claim_text(span_nodes, "*");
			span_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "required svelte-o7fd5j");
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
			append_hydration(span, t);
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (216:16) {#if required}
function create_if_block_4(ctx) {
	let span;
	let t;

	return {
		c() {
			span = element("span");
			t = text("*");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t = claim_text(span_nodes, "*");
			span_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "required svelte-o7fd5j");
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
			append_hydration(span, t);
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (197:16) {#if required}
function create_if_block_2(ctx) {
	let span;
	let t;

	return {
		c() {
			span = element("span");
			t = text("*");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t = claim_text(span_nodes, "*");
			span_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "required svelte-o7fd5j");
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
			append_hydration(span, t);
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (191:8) {#each fields as { label, type, placeholder, required }
function create_each_block(ctx) {
	let current_block_type_index;
	let if_block;
	let if_block_anchor;
	let current;
	const if_block_creators = [create_if_block_1, create_if_block_3, create_else_block];
	const if_blocks = [];

	function select_block_type_1(ctx, dirty) {
		if (/*type*/ ctx[16] === "file") return 0;
		if (/*type*/ ctx[16] === "textarea") return 1;
		return 2;
	}

	current_block_type_index = select_block_type_1(ctx);
	if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_blocks[current_block_type_index].m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
			current = true;
		},
		p(ctx, dirty) {
			let previous_block_index = current_block_type_index;
			current_block_type_index = select_block_type_1(ctx);

			if (current_block_type_index === previous_block_index) {
				if_blocks[current_block_type_index].p(ctx, dirty);
			} else {
				group_outros();

				transition_out(if_blocks[previous_block_index], 1, 1, () => {
					if_blocks[previous_block_index] = null;
				});

				check_outros();
				if_block = if_blocks[current_block_type_index];

				if (!if_block) {
					if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
					if_block.c();
				} else {
					if_block.p(ctx, dirty);
				}

				transition_in(if_block, 1);
				if_block.m(if_block_anchor.parentNode, if_block_anchor);
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block);
			current = true;
		},
		o(local) {
			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if_blocks[current_block_type_index].d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function create_fragment(ctx) {
	let section;
	let current_block_type_index;
	let if_block;
	let t0;
	let svg0;
	let path0;
	let t1;
	let svg1;
	let path1;
	let current;
	const if_block_creators = [create_if_block, create_if_block_6, create_if_block_7];
	const if_blocks = [];

	function select_block_type(ctx, dirty) {
		if (!/*submitted*/ ctx[6] && !/*error*/ ctx[7]) return 0;
		if (/*submitted*/ ctx[6]) return 1;
		if (/*error*/ ctx[7]) return 2;
		return -1;
	}

	if (~(current_block_type_index = select_block_type(ctx))) {
		if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
	}

	return {
		c() {
			section = element("section");
			if (if_block) if_block.c();
			t0 = space();
			svg0 = svg_element("svg");
			path0 = svg_element("path");
			t1 = space();
			svg1 = svg_element("svg");
			path1 = svg_element("path");
			this.h();
		},
		l(nodes) {
			section = claim_element(nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			if (if_block) if_block.l(section_nodes);
			t0 = claim_space(section_nodes);

			svg0 = claim_svg_element(section_nodes, "svg", {
				viewBox: true,
				fill: true,
				xmlns: true,
				class: true
			});

			var svg0_nodes = children(svg0);
			path0 = claim_svg_element(svg0_nodes, "path", { d: true, fill: true, class: true });
			children(path0).forEach(detach);
			svg0_nodes.forEach(detach);
			t1 = claim_space(section_nodes);

			svg1 = claim_svg_element(section_nodes, "svg", {
				viewBox: true,
				fill: true,
				xmlns: true,
				class: true
			});

			var svg1_nodes = children(svg1);
			path1 = claim_svg_element(svg1_nodes, "path", { d: true, fill: true, class: true });
			children(path1).forEach(detach);
			svg1_nodes.forEach(detach);
			section_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(path0, "d", "M85.5 1.01958e-06C62.824 7.49169e-07 41.0767 9.00801 25.0424 25.0424C9.00801 41.0767 3.00198e-06 62.824 1.01958e-06 85.5C-9.62822e-07 108.176 9.00801 129.923 25.0424 145.958C41.0767 161.992 62.824 171 85.5 171L85.5 85.5L85.5 1.01958e-06Z");
			attr(path0, "fill", "var(--color-shade)");
			attr(path0, "class", "svelte-o7fd5j");
			attr(svg0, "viewBox", "0 0 86 171");
			attr(svg0, "fill", "none");
			attr(svg0, "xmlns", "http://www.w3.org/2000/svg");
			attr(svg0, "class", "svelte-o7fd5j");
			attr(path1, "d", "M0.499993 171C23.176 171 44.9233 161.992 60.9576 145.958C76.992 129.923 86 108.176 86 85.5C86 62.824 76.992 41.0767 60.9576 25.0424C44.9233 9.00801 23.176 6.7786e-07 0.500013 -3.73732e-06L0.499996 85.5L0.499993 171Z");
			attr(path1, "fill", "var(--color-shade)");
			attr(path1, "class", "svelte-o7fd5j");
			attr(svg1, "viewBox", "0 0 86 171");
			attr(svg1, "fill", "none");
			attr(svg1, "xmlns", "http://www.w3.org/2000/svg");
			attr(svg1, "class", "svelte-o7fd5j");
			attr(section, "class", "svelte-o7fd5j");
		},
		m(target, anchor) {
			insert_hydration(target, section, anchor);

			if (~current_block_type_index) {
				if_blocks[current_block_type_index].m(section, null);
			}

			append_hydration(section, t0);
			append_hydration(section, svg0);
			append_hydration(svg0, path0);
			append_hydration(section, t1);
			append_hydration(section, svg1);
			append_hydration(svg1, path1);
			current = true;
		},
		p(ctx, [dirty]) {
			let previous_block_index = current_block_type_index;
			current_block_type_index = select_block_type(ctx);

			if (current_block_type_index === previous_block_index) {
				if (~current_block_type_index) {
					if_blocks[current_block_type_index].p(ctx, dirty);
				}
			} else {
				if (if_block) {
					group_outros();

					transition_out(if_blocks[previous_block_index], 1, 1, () => {
						if_blocks[previous_block_index] = null;
					});

					check_outros();
				}

				if (~current_block_type_index) {
					if_block = if_blocks[current_block_type_index];

					if (!if_block) {
						if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
						if_block.c();
					} else {
						if_block.p(ctx, dirty);
					}

					transition_in(if_block, 1);
					if_block.m(section, t0);
				} else {
					if_block = null;
				}
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block);
			current = true;
		},
		o(local) {
			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(section);

			if (~current_block_type_index) {
				if_blocks[current_block_type_index].d();
			}
		}
	};
}

function get_form_data(form) {
	const form_data = new FormData(form);
	var object = {};

	form_data.forEach((value, key) => {
		object[key] = value;
	});

	return object;
}

function instance($$self, $$props, $$invalidate) {
	let { props } = $$props;
	let { fields } = $$props;
	let { submit } = $$props;
	let { heading } = $$props;
	let { footer_text } = $$props;
	let { form_endpoint } = $$props;
	let { submission_confirmation } = $$props;

	// Store file names to display them in the file field
	const files = {};

	function add_file({ id, e }) {
		const file_name = e.target.value.split("\\").pop();
		$$invalidate(5, files[id] = file_name, files);
	}

	let submitted = false;
	let error = false;

	async function submit_form(e) {
		const form_data = get_form_data(e.target);
		const { data } = await axios.post(form_endpoint, form_data).catch(e => ({ data: null }));

		if (data) {
			$$invalidate(6, submitted = true);
		} else {
			$$invalidate(7, error = true);
		}
	}

	const change_handler = (id, e) => add_file({ id, e });
	const click_handler = () => $$invalidate(6, submitted = false);
	const click_handler_1 = () => $$invalidate(7, error = false);

	$$self.$$set = $$props => {
		if ('props' in $$props) $$invalidate(10, props = $$props.props);
		if ('fields' in $$props) $$invalidate(0, fields = $$props.fields);
		if ('submit' in $$props) $$invalidate(1, submit = $$props.submit);
		if ('heading' in $$props) $$invalidate(2, heading = $$props.heading);
		if ('footer_text' in $$props) $$invalidate(3, footer_text = $$props.footer_text);
		if ('form_endpoint' in $$props) $$invalidate(11, form_endpoint = $$props.form_endpoint);
		if ('submission_confirmation' in $$props) $$invalidate(4, submission_confirmation = $$props.submission_confirmation);
	};

	return [
		fields,
		submit,
		heading,
		footer_text,
		submission_confirmation,
		files,
		submitted,
		error,
		add_file,
		submit_form,
		props,
		form_endpoint,
		change_handler,
		click_handler,
		click_handler_1
	];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance, create_fragment, safe_not_equal, {
			props: 10,
			fields: 0,
			submit: 1,
			heading: 2,
			footer_text: 3,
			form_endpoint: 11,
			submission_confirmation: 4
		});
	}
}

export { Component as default };
