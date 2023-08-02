function noop() { }
const identity = x => x;
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
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
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

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
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
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
    return style.sheet;
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
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function toggle_class(element, name, toggle) {
    element.classList[toggle ? 'add' : 'remove'](name);
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}
function head_selector(nodeId, head) {
    const result = [];
    let started = 0;
    for (const node of head.childNodes) {
        if (node.nodeType === 8 /* comment node */) {
            const comment = node.textContent.trim();
            if (comment === `HEAD_${nodeId}_END`) {
                started -= 1;
                result.push(node);
            }
            else if (comment === `HEAD_${nodeId}_START`) {
                started += 1;
                result.push(node);
            }
        }
        else if (started > 0) {
            result.push(node);
        }
    }
    return result;
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { ownerNode } = info.stylesheet;
            // there is no ownerNode if it runs on jsdom.
            if (ownerNode)
                detach(ownerNode);
        });
        managed_styles.clear();
    });
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

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
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
const null_transition = { duration: 0 };
function create_bidirectional_transition(node, fn, params, intro) {
    const options = { direction: 'both' };
    let config = fn(node, params, options);
    let t = intro ? 0 : 1;
    let running_program = null;
    let pending_program = null;
    let animation_name = null;
    function clear_animation() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function init(program, duration) {
        const d = (program.b - t);
        duration *= Math.abs(d);
        return {
            a: t,
            b: program.b,
            d,
            duration,
            start: program.start,
            end: program.start + duration,
            group: program.group
        };
    }
    function go(b) {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        const program = {
            start: now() + delay,
            b
        };
        if (!b) {
            // @ts-ignore todo: improve typings
            program.group = outros;
            outros.r += 1;
        }
        if (running_program || pending_program) {
            pending_program = program;
        }
        else {
            // if this is an intro, and there's a delay, we need to do
            // an initial tick and/or apply CSS animation immediately
            if (css) {
                clear_animation();
                animation_name = create_rule(node, t, b, duration, delay, easing, css);
            }
            if (b)
                tick(0, 1);
            running_program = init(program, duration);
            add_render_callback(() => dispatch(node, b, 'start'));
            loop(now => {
                if (pending_program && now > pending_program.start) {
                    running_program = init(pending_program, duration);
                    pending_program = null;
                    dispatch(node, running_program.b, 'start');
                    if (css) {
                        clear_animation();
                        animation_name = create_rule(node, t, running_program.b, running_program.duration, 0, easing, config.css);
                    }
                }
                if (running_program) {
                    if (now >= running_program.end) {
                        tick(t = running_program.b, 1 - t);
                        dispatch(node, running_program.b, 'end');
                        if (!pending_program) {
                            // we're done
                            if (running_program.b) {
                                // intro — we can tidy up immediately
                                clear_animation();
                            }
                            else {
                                // outro — needs to be coordinated
                                if (!--running_program.group.r)
                                    run_all(running_program.group.c);
                            }
                        }
                        running_program = null;
                    }
                    else if (now >= running_program.start) {
                        const p = now - running_program.start;
                        t = running_program.a + running_program.d * easing(p / running_program.duration);
                        tick(t, 1 - t);
                    }
                }
                return !!(running_program || pending_program);
            });
        }
    }
    return {
        run(b) {
            if (is_function(config)) {
                wait().then(() => {
                    // @ts-ignore
                    config = config(options);
                    go(b);
                });
            }
            else {
                go(b);
            }
        },
        end() {
            clear_animation();
            running_program = pending_program = null;
        }
    };
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

/* generated by Svelte v3.59.1 */

function create_fragment(ctx) {
	let meta0;
	let meta1;
	let link0;
	let link1;
	let title_value;
	let meta2;
	let style;
	let t;
	document.title = title_value = /*title*/ ctx[0];

	return {
		c() {
			meta0 = element("meta");
			meta1 = element("meta");
			link0 = element("link");
			link1 = element("link");
			meta2 = element("meta");
			style = element("style");
			t = text("@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n\nhtml {\n  /* Theme */\n  --color-accent: #716996;\n  --color-shade: #e2e1ea;\n\n  --font-heading: \"Fredoka\", sans-serif;\n  --font-base: \"Lato\", sans-serif;\n\n  /* Default property values */\n  --background: #f4f3f0;\n  --color: #333;\n  --padding: 2rem;\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --max-width: 1250px;\n  --border-color: #cbcace;\n  --transition-time: 0.1s;\n  --transition: var(--transition-time) color,\n    var(--transition-time) background-color, var(--transition-time) border-color,\n    var(--transition-time) text-decoration-color,\n    var(--transition-time) box-shadow, var(--transtion-time) transform;\n}\n\n#page {\n  font-family: var(--font-base);\n  color: var(--color);\n  line-height: 1.6;\n  font-size: 1.25rem;\n  font-weight: 300;\n  background: var(--background);\n}\n\n.content {\n  max-width: 800px;\n  margin: 0 auto;\n  padding: 4rem 2rem;\n}\n\n.content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.content > p {\n    line-height: 1.5;\n    margin-bottom: 1.5rem;\n  }\n\n.content a {\n  }\n\n.content h1 {\n    font-family: var(--font-heading);\n    font-size: 2.75rem;\n    font-weight: 500;\n    line-height: 1.1;\n    margin-bottom: 1.5rem;\n  }\n\n.content h2 {\n    font-family: var(--font-heading);\n    font-size: 2.5rem;\n    font-weight: 500;\n    line-height: 1.1;\n    margin-bottom: 1rem;\n  }\n\n.content h3 {\n    font-family: var(--font-heading);\n    font-size: 2.25rem;\n    font-weight: 500;\n    margin-bottom: 0.5rem;\n    line-height: 1.1;\n  }\n\n.content ul {\n    list-style: disc;\n    padding-bottom: 1.5rem;\n    padding-left: 1.25rem;\n  }\n\n.content ol {\n    list-style: decimal;\n    padding-bottom: 1.5rem;\n    padding-left: 1.25rem;\n    margin-bottom: 1rem;\n  }\n\n.content blockquote {\n    padding: 2rem;\n    margin-bottom: 1.5rem;\n    border-left: 5px solid var(--color-accent);\n  }\n\n.section-container {\n  width: 100%;\n  max-width: var(--max-width, 1200px);\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n\n.heading {\n  font-family: var(--font-heading);\n  font-size: 2.5rem;\n  line-height: 1.1;\n  font-weight: 500;\n  color: #333;\n}\n\n@media (min-width: 800px) {\n\n.heading {\n    font-size: 2.75rem\n}\n  }\n\n.button {\n  color: #f6f6f9;\n  font-size: 1rem;\n  font-weight: 500;\n  border-radius: 2rem;\n  padding: 10px 24px;\n\n  background: var(--color-accent);\n  transition: var(--transition);\n  white-space: nowrap;\n}\n\n.button:hover {\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent);\n    border: 2px solid var(--color-accent);\n  }\n\n@-webkit-keyframes pulse {\n  from {\n    transform: scale(0.75);\n  }\n\n  to {\n    transform: scale(1);\n  }\n}\n\n@keyframes pulse {\n  from {\n    transform: scale(0.75);\n  }\n\n  to {\n    transform: scale(1);\n  }\n}\n\n/* Screen-readers only */\n.sr-only {\n  position: absolute;\n  width: 1px;\n  height: 1px;\n  padding: 0;\n  margin: -1px;\n  overflow: hidden;\n  clip: rect(0, 0, 0, 0);\n  white-space: nowrap;\n  border-width: 0;\n}");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-1lw70r8', document.head);
			meta0 = claim_element(head_nodes, "META", { name: true, content: true });
			meta1 = claim_element(head_nodes, "META", { charset: true });
			link0 = claim_element(head_nodes, "LINK", { rel: true, href: true });
			link1 = claim_element(head_nodes, "LINK", { href: true, rel: true });
			meta2 = claim_element(head_nodes, "META", { name: true, content: true });
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t = claim_text(style_nodes, "@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n\nhtml {\n  /* Theme */\n  --color-accent: #716996;\n  --color-shade: #e2e1ea;\n\n  --font-heading: \"Fredoka\", sans-serif;\n  --font-base: \"Lato\", sans-serif;\n\n  /* Default property values */\n  --background: #f4f3f0;\n  --color: #333;\n  --padding: 2rem;\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --max-width: 1250px;\n  --border-color: #cbcace;\n  --transition-time: 0.1s;\n  --transition: var(--transition-time) color,\n    var(--transition-time) background-color, var(--transition-time) border-color,\n    var(--transition-time) text-decoration-color,\n    var(--transition-time) box-shadow, var(--transtion-time) transform;\n}\n\n#page {\n  font-family: var(--font-base);\n  color: var(--color);\n  line-height: 1.6;\n  font-size: 1.25rem;\n  font-weight: 300;\n  background: var(--background);\n}\n\n.content {\n  max-width: 800px;\n  margin: 0 auto;\n  padding: 4rem 2rem;\n}\n\n.content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.content > p {\n    line-height: 1.5;\n    margin-bottom: 1.5rem;\n  }\n\n.content a {\n  }\n\n.content h1 {\n    font-family: var(--font-heading);\n    font-size: 2.75rem;\n    font-weight: 500;\n    line-height: 1.1;\n    margin-bottom: 1.5rem;\n  }\n\n.content h2 {\n    font-family: var(--font-heading);\n    font-size: 2.5rem;\n    font-weight: 500;\n    line-height: 1.1;\n    margin-bottom: 1rem;\n  }\n\n.content h3 {\n    font-family: var(--font-heading);\n    font-size: 2.25rem;\n    font-weight: 500;\n    margin-bottom: 0.5rem;\n    line-height: 1.1;\n  }\n\n.content ul {\n    list-style: disc;\n    padding-bottom: 1.5rem;\n    padding-left: 1.25rem;\n  }\n\n.content ol {\n    list-style: decimal;\n    padding-bottom: 1.5rem;\n    padding-left: 1.25rem;\n    margin-bottom: 1rem;\n  }\n\n.content blockquote {\n    padding: 2rem;\n    margin-bottom: 1.5rem;\n    border-left: 5px solid var(--color-accent);\n  }\n\n.section-container {\n  width: 100%;\n  max-width: var(--max-width, 1200px);\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n\n.heading {\n  font-family: var(--font-heading);\n  font-size: 2.5rem;\n  line-height: 1.1;\n  font-weight: 500;\n  color: #333;\n}\n\n@media (min-width: 800px) {\n\n.heading {\n    font-size: 2.75rem\n}\n  }\n\n.button {\n  color: #f6f6f9;\n  font-size: 1rem;\n  font-weight: 500;\n  border-radius: 2rem;\n  padding: 10px 24px;\n\n  background: var(--color-accent);\n  transition: var(--transition);\n  white-space: nowrap;\n}\n\n.button:hover {\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent);\n    border: 2px solid var(--color-accent);\n  }\n\n@-webkit-keyframes pulse {\n  from {\n    transform: scale(0.75);\n  }\n\n  to {\n    transform: scale(1);\n  }\n}\n\n@keyframes pulse {\n  from {\n    transform: scale(0.75);\n  }\n\n  to {\n    transform: scale(1);\n  }\n}\n\n/* Screen-readers only */\n.sr-only {\n  position: absolute;\n  width: 1px;\n  height: 1px;\n  padding: 0;\n  margin: -1px;\n  overflow: hidden;\n  clip: rect(0, 0, 0, 0);\n  white-space: nowrap;\n  border-width: 0;\n}");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(meta0, "name", "viewport");
			attr(meta0, "content", "width=device-width, initial-scale=1.0");
			attr(meta1, "charset", "UTF-8");
			attr(link0, "rel", "preconnect");
			attr(link0, "href", "https://fonts.bunny.net");
			attr(link1, "href", "https://fonts.bunny.net/css?family=fredoka:300,400,500,600,700|lato:300,400,700,900");
			attr(link1, "rel", "stylesheet");
			attr(meta2, "name", "description");
			attr(meta2, "content", /*description*/ ctx[1]);
		},
		m(target, anchor) {
			append_hydration(document.head, meta0);
			append_hydration(document.head, meta1);
			append_hydration(document.head, link0);
			append_hydration(document.head, link1);
			append_hydration(document.head, meta2);
			append_hydration(document.head, style);
			append_hydration(style, t);
		},
		p(ctx, [dirty]) {
			if (dirty & /*title*/ 1 && title_value !== (title_value = /*title*/ ctx[0])) {
				document.title = title_value;
			}

			if (dirty & /*description*/ 2) {
				attr(meta2, "content", /*description*/ ctx[1]);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			detach(meta0);
			detach(meta1);
			detach(link0);
			detach(link1);
			detach(meta2);
			detach(style);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { social } = $$props;
	let { site_footer } = $$props;
	let { title } = $$props;
	let { description } = $$props;

	$$self.$$set = $$props => {
		if ('social' in $$props) $$invalidate(2, social = $$props.social);
		if ('site_footer' in $$props) $$invalidate(3, site_footer = $$props.site_footer);
		if ('title' in $$props) $$invalidate(0, title = $$props.title);
		if ('description' in $$props) $$invalidate(1, description = $$props.description);
	};

	return [title, description, social, site_footer];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance, create_fragment, safe_not_equal, {
			social: 2,
			site_footer: 3,
			title: 0,
			description: 1
		});
	}
}

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
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
const defaultIconDimensions = Object.freeze({
  left: 0,
  top: 0,
  width: 16,
  height: 16
});
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
    currentProps = mergeIconData(icons[name2] || aliases[name2], currentProps);
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
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(icon, defaultExtendedIconProps)) {
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
function addIconSet(storage2, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage2.icons[name] = icon;
    } else {
      storage2.missing.add(name);
    }
  });
}
function addIconToStorage(storage2, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage2.icons[name] = {...icon};
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
    const storage2 = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage2.icons[iconName] || (storage2.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage2 = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage2, icon.name, data);
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
  const storage2 = getStorage(provider, prefix);
  return !!addIconSet(storage2, data);
}
const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  ...defaultIconSizeCustomisations,
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
        transformations.push("translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")");
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push("translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")");
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
        transformations.unshift("rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
      case 2:
        transformations.unshift("rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")");
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift("rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")");
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
      body = '<g transform="' + transformations.join(" ") + '">' + body + "</g>";
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
  attributes.viewBox = box.left.toString() + " " + box.top.toString() + " " + boxWidth.toString() + " " + boxHeight.toString();
  return {
    attributes,
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
    body = body.replace(new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"), "$1" + newID + suffix + "$3");
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
    resources,
    path: source.path || "/",
    maxURL: source.maxURL || 500,
    rotate: source.rotate || 750,
    timeout: source.timeout || 5e3,
    random: source.random === true,
    index: source.index || 0,
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
  const storage2 = /* @__PURE__ */ Object.create(null);
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
    const providerStorage = storage2[provider] || (storage2[provider] = /* @__PURE__ */ Object.create(null));
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
  storages.forEach((storage2) => {
    const items = storage2.loaderCallbacks;
    if (items) {
      storage2.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage2) {
  if (!storage2.pendingCallbacksFlag) {
    storage2.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage2.pendingCallbacksFlag = false;
      const items = storage2.loaderCallbacks ? storage2.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage2.provider;
      const prefix = storage2.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage2.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage2.missing.has(name)) {
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
            removeCallback([storage2], item.id);
          }
          item.callback(icons.loaded.slice(0), icons.missing.slice(0), icons.pending.slice(0), item.abort);
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
  pendingSources.forEach((storage2) => {
    (storage2.loaderCallbacks || (storage2.loaderCallbacks = [])).push(item);
  });
  return abort;
}
function listToIcons(list, validate = true, simpleNames2 = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames2) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};
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
    const query2 = sendQuery(config, payload, queryCallback, (data, error) => {
      cleanup();
      if (doneCallback) {
        doneCallback(data, error);
      }
    });
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
  let send2;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send2 = api.send;
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
        send2 = api.send;
      }
    }
  }
  if (!redundancy || !send2) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send2, callback)().abort;
}
const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
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
function setBrowserStorageItemsCount(storage2, value) {
  return setStoredItem(storage2, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage2) {
  return parseInt(getStoredItem(storage2, browserCacheCountKey)) || 0;
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
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && callback(data, index)) {
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
      const storage2 = getStorage(provider, prefix);
      if (!addIconSet(storage2, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage2.lastModifiedCached = storage2.lastModifiedCached ? Math.min(storage2.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}
function updateLastModified(storage2, lastModified) {
  const lastValue = storage2.lastModifiedCached;
  if (lastValue && lastValue >= lastModified) {
    return lastValue === lastModified;
  }
  storage2.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage2.provider || iconSet.prefix !== storage2.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage2, data) {
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
      if (!setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage2.provider,
      data
    };
    return setStoredItem(func, browserCachePrefix + index.toString(), JSON.stringify(item));
  }
  if (data.lastModified && !updateLastModified(storage2, data.lastModified)) {
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
function loadedNewIcons(storage2) {
  if (!storage2.iconsLoaderFlag) {
    storage2.iconsLoaderFlag = true;
    setTimeout(() => {
      storage2.iconsLoaderFlag = false;
      updateCallbacks(storage2);
    });
  }
}
function loadNewIcons(storage2, icons) {
  if (!storage2.iconsToLoad) {
    storage2.iconsToLoad = icons;
  } else {
    storage2.iconsToLoad = storage2.iconsToLoad.concat(icons).sort();
  }
  if (!storage2.iconsQueueFlag) {
    storage2.iconsQueueFlag = true;
    setTimeout(() => {
      storage2.iconsQueueFlag = false;
      const {provider, prefix} = storage2;
      const icons2 = storage2.iconsToLoad;
      delete storage2.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage2.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(storage2, data);
              if (!parsed.length) {
                return;
              }
              const pending = storage2.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage2, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage2);
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
          callback(sortedIcons.loaded, sortedIcons.missing, sortedIcons.pending, emptyCallback);
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
    const {provider, prefix} = icon;
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
    const {provider, prefix, name} = icon;
    const storage2 = getStorage(provider, prefix);
    const pendingQueue = storage2.pendingIcons || (storage2.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage2) => {
    const {provider, prefix} = storage2;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage2, newIcons[provider][prefix]);
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
  inline: false
};
const svgDefaults = {
  xmlns: "http://www.w3.org/2000/svg",
  "xmlns:xlink": "http://www.w3.org/1999/xlink",
  "aria-hidden": true,
  role: "img"
};
const commonProps = {
  display: "inline-block"
};
const monotoneProps = {
  "background-color": "currentColor"
};
const coloredProps = {
  "background-color": "transparent"
};
const propsToAdd = {
  image: "var(--svg)",
  repeat: "no-repeat",
  size: "100% 100%"
};
const propsToAddTo = {
  "-webkit-mask": monotoneProps,
  mask: monotoneProps,
  background: coloredProps
};
for (const prefix in propsToAddTo) {
  const list = propsToAddTo[prefix];
  for (const prop in propsToAdd) {
    list[prefix + "-" + prop] = propsToAdd[prop];
  }
}
function fixSize(value) {
  return value + (value.match(/^[-0-9.]+$/) ? "px" : "");
}
function render(icon, props) {
  const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
  const mode = props.mode || "svg";
  const componentProps = mode === "svg" ? {...svgDefaults} : {};
  if (icon.body.indexOf("xlink:") === -1) {
    delete componentProps["xmlns:xlink"];
  }
  let style = typeof props.style === "string" ? props.style : "";
  for (let key in props) {
    const value = props[key];
    if (value === void 0) {
      continue;
    }
    switch (key) {
      case "icon":
      case "style":
      case "onLoad":
      case "mode":
        break;
      case "inline":
      case "hFlip":
      case "vFlip":
        customisations[key] = value === true || value === "true" || value === 1;
        break;
      case "flip":
        if (typeof value === "string") {
          flipFromString(customisations, value);
        }
        break;
      case "color":
        style = style + (style.length > 0 && style.trim().slice(-1) !== ";" ? ";" : "") + "color: " + value + "; ";
        break;
      case "rotate":
        if (typeof value === "string") {
          customisations[key] = rotateFromString(value);
        } else if (typeof value === "number") {
          customisations[key] = value;
        }
        break;
      case "ariaHidden":
      case "aria-hidden":
        if (value !== true && value !== "true") {
          delete componentProps["aria-hidden"];
        }
        break;
      default:
        if (key.slice(0, 3) === "on:") {
          break;
        }
        if (defaultExtendedIconCustomisations[key] === void 0) {
          componentProps[key] = value;
        }
    }
  }
  const item = iconToSVG(icon, customisations);
  const renderAttribs = item.attributes;
  if (customisations.inline) {
    style = "vertical-align: -0.125em; " + style;
  }
  if (mode === "svg") {
    Object.assign(componentProps, renderAttribs);
    if (style !== "") {
      componentProps.style = style;
    }
    let localCounter = 0;
    let id = props.id;
    if (typeof id === "string") {
      id = id.replace(/-/g, "_");
    }
    return {
      svg: true,
      attributes: componentProps,
      body: replaceIDs(item.body, id ? () => id + "ID" + localCounter++ : "iconifySvelte")
    };
  }
  const {body, width, height} = icon;
  const useMask = mode === "mask" || (mode === "bg" ? false : body.indexOf("currentColor") !== -1);
  const html = iconToHTML(body, {
    ...renderAttribs,
    width: width + "",
    height: height + ""
  });
  const url = svgToURL(html);
  const styles = {
    "--svg": url
  };
  const size = (prop) => {
    const value = renderAttribs[prop];
    if (value) {
      styles[prop] = fixSize(value);
    }
  };
  size("width");
  size("height");
  Object.assign(styles, commonProps, useMask ? monotoneProps : coloredProps);
  let customStyle = "";
  for (const key in styles) {
    customStyle += key + ": " + styles[key] + ";";
  }
  componentProps.style = customStyle + style;
  return {
    svg: false,
    attributes: componentProps
  };
}
allowSimpleNames(true);
setAPIModule("", fetchAPIModule);
if (typeof document !== "undefined" && typeof window !== "undefined") {
  initBrowserStorage();
  const _window2 = window;
  if (_window2.IconifyPreload !== void 0) {
    const preload = _window2.IconifyPreload;
    const err = "Invalid IconifyPreload syntax.";
    if (typeof preload === "object" && preload !== null) {
      (preload instanceof Array ? preload : [preload]).forEach((item) => {
        try {
          if (typeof item !== "object" || item === null || item instanceof Array || typeof item.icons !== "object" || typeof item.prefix !== "string" || !addCollection(item)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      });
    }
  }
  if (_window2.IconifyProviders !== void 0) {
    const providers = _window2.IconifyProviders;
    if (typeof providers === "object" && providers !== null) {
      for (let key in providers) {
        const err = "IconifyProviders[" + key + "] is invalid.";
        try {
          const value = providers[key];
          if (typeof value !== "object" || !value || value.resources === void 0) {
            continue;
          }
          if (!addAPIProvider(key, value)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      }
    }
  }
}
function checkIconState(icon, state, mounted, callback, onload) {
  function abortLoading() {
    if (state.loading) {
      state.loading.abort();
      state.loading = null;
    }
  }
  if (typeof icon === "object" && icon !== null && typeof icon.body === "string") {
    state.name = "";
    abortLoading();
    return {data: {...defaultIconProps, ...icon}};
  }
  let iconName;
  if (typeof icon !== "string" || (iconName = stringToIcon(icon, false, true)) === null) {
    abortLoading();
    return null;
  }
  const data = getIconData(iconName);
  if (!data) {
    if (mounted && (!state.loading || state.loading.name !== icon)) {
      abortLoading();
      state.name = "";
      state.loading = {
        name: icon,
        abort: loadIcons([iconName], callback)
      };
    }
    return null;
  }
  abortLoading();
  if (state.name !== icon) {
    state.name = icon;
    if (onload && !state.destroyed) {
      onload(icon);
    }
  }
  const classes = ["iconify"];
  if (iconName.prefix !== "") {
    classes.push("iconify--" + iconName.prefix);
  }
  if (iconName.provider !== "") {
    classes.push("iconify--" + iconName.provider);
  }
  return {data, classes};
}
function generateIcon(icon, props) {
  return icon ? render({
    ...defaultIconProps,
    ...icon
  }, props) : null;
}
var checkIconState_1 = checkIconState;
var generateIcon_1 = generateIcon;

/* generated by Svelte v3.59.1 */

function create_if_block(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1;
		return create_else_block;
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

// (113:1) {:else}
function create_else_block(ctx) {
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

// (109:1) {#if data.svg}
function create_if_block_1(ctx) {
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
	let if_block = /*data*/ ctx[0] && create_if_block(ctx);

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
					if_block = create_if_block(ctx);
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
			const iconData = checkIconState_1($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon_1(iconData.data, $$props) : null);

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

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
}

/* generated by Svelte v3.59.1 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[11] = list[i].link;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[11] = list[i].link;
	return child_ctx;
}

function get_each_context_2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[11] = list[i].link;
	return child_ctx;
}

// (175:6) {#each site_nav.left as { link }}
function create_each_block_2(ctx) {
	let a;
	let t_value = /*link*/ ctx[11].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-6hkp3j");
			attr(a, "href", a_href_value = /*link*/ ctx[11].url);
			toggle_class(a, "active", /*link*/ ctx[11].url === window.location.pathname);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[11].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[11].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*site_nav, window*/ 2) {
				toggle_class(a, "active", /*link*/ ctx[11].url === window.location.pathname);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (184:6) {#each site_nav.right as { link }}
function create_each_block_1(ctx) {
	let a;
	let t_value = /*link*/ ctx[11].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-6hkp3j");
			attr(a, "href", a_href_value = /*link*/ ctx[11].url);
			toggle_class(a, "active", /*link*/ ctx[11].url === window.location.pathname);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[11].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[11].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*site_nav, window*/ 2) {
				toggle_class(a, "active", /*link*/ ctx[11].url === window.location.pathname);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (199:4) {#if mobileNavOpen}
function create_if_block$1(ctx) {
	let nav;
	let a;
	let img;
	let img_src_value;
	let img_alt_value;
	let t0;
	let t1;
	let button;
	let icon;
	let nav_transition;
	let current;
	let mounted;
	let dispose;
	let each_value = [.../*site_nav*/ ctx[1].left, .../*site_nav*/ ctx[1].right];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	icon = new Component$1({ props: { height: "25", icon: "bi:x-lg" } });

	return {
		c() {
			nav = element("nav");
			a = element("a");
			img = element("img");
			t0 = space();

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t1 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			nav = claim_element(nodes, "NAV", { id: true, class: true });
			var nav_nodes = children(nav);
			a = claim_element(nav_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			img = claim_element(a_nodes, "IMG", { src: true, alt: true });
			a_nodes.forEach(detach);
			t0 = claim_space(nav_nodes);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t1 = claim_space(nav_nodes);

			button = claim_element(nav_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].alt);
			attr(a, "href", "/");
			attr(a, "class", "logo svelte-6hkp3j");
			attr(button, "id", "close");
			attr(button, "aria-label", "Close Navigation");
			attr(button, "class", "svelte-6hkp3j");
			attr(nav, "id", "popup");
			attr(nav, "class", "svelte-6hkp3j");
		},
		m(target, anchor) {
			insert_hydration(target, nav, anchor);
			append_hydration(nav, a);
			append_hydration(a, img);
			append_hydration(nav, t0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t1);
			append_hydration(nav, button);
			mount_component(icon, button, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[9]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (!current || dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].url)) {
				attr(img, "src", img_src_value);
			}

			if (!current || dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*site_nav, window*/ 2) {
				each_value = [.../*site_nav*/ ctx[1].left, .../*site_nav*/ ctx[1].right];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t1);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			add_render_callback(() => {
				if (!current) return;
				if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, true);
				nav_transition.run(1);
			});

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, false);
			nav_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(nav);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			if (detaching && nav_transition) nav_transition.end();
			mounted = false;
			dispose();
		}
	};
}

// (204:8) {#each [...site_nav.left, ...site_nav.right] as { link }}
function create_each_block(ctx) {
	let a;
	let t_value = /*link*/ ctx[11].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[11].url);
			attr(a, "class", "svelte-6hkp3j");
			toggle_class(a, "active", /*link*/ ctx[11].url === window.location.pathname);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[11].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[11].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*site_nav, window*/ 2) {
				toggle_class(a, "active", /*link*/ ctx[11].url === window.location.pathname);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$2(ctx) {
	let div3;
	let div0;
	let a0;
	let icon0;
	let t0;
	let span0;
	let t1_value = /*contacts*/ ctx[2].phone + "";
	let t1;
	let a0_href_value;
	let t2;
	let a1;
	let icon1;
	let t3;
	let span1;
	let t4_value = /*contacts*/ ctx[2].address + "";
	let t4;
	let a1_href_value;
	let t5;
	let header;
	let div1;
	let nav0;
	let t6;
	let a2;
	let span2;
	let t7_value = /*logo*/ ctx[0].alt + "";
	let t7;
	let t8;
	let img0;
	let img0_src_value;
	let img0_alt_value;
	let t9;
	let nav1;
	let t10;
	let div2;
	let a3;
	let img1;
	let img1_src_value;
	let img1_alt_value;
	let t11;
	let button;
	let icon2;
	let t12;
	let current;
	let mounted;
	let dispose;

	icon0 = new Component$1({
			props: { icon: "material-symbols:phone-enabled" }
		});

	icon1 = new Component$1({
			props: {
				icon: "material-symbols:location-on-rounded"
			}
		});

	let each_value_2 = /*site_nav*/ ctx[1].left;
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_2.length; i += 1) {
		each_blocks_1[i] = create_each_block_2(get_each_context_2(ctx, each_value_2, i));
	}

	let each_value_1 = /*site_nav*/ ctx[1].right;
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	icon2 = new Component$1({
			props: { height: "30", icon: "eva:menu-outline" }
		});

	let if_block = /*mobileNavOpen*/ ctx[3] && create_if_block$1(ctx);

	return {
		c() {
			div3 = element("div");
			div0 = element("div");
			a0 = element("a");
			create_component(icon0.$$.fragment);
			t0 = space();
			span0 = element("span");
			t1 = text(t1_value);
			t2 = space();
			a1 = element("a");
			create_component(icon1.$$.fragment);
			t3 = space();
			span1 = element("span");
			t4 = text(t4_value);
			t5 = space();
			header = element("header");
			div1 = element("div");
			nav0 = element("nav");

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t6 = space();
			a2 = element("a");
			span2 = element("span");
			t7 = text(t7_value);
			t8 = space();
			img0 = element("img");
			t9 = space();
			nav1 = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t10 = space();
			div2 = element("div");
			a3 = element("a");
			img1 = element("img");
			t11 = space();
			button = element("button");
			create_component(icon2.$$.fragment);
			t12 = space();
			if (if_block) if_block.c();
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			div0 = claim_element(div3_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			a0 = claim_element(div0_nodes, "A", {
				class: true,
				href: true,
				"aria-label": true
			});

			var a0_nodes = children(a0);
			claim_component(icon0.$$.fragment, a0_nodes);
			t0 = claim_space(a0_nodes);
			span0 = claim_element(a0_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t1 = claim_text(span0_nodes, t1_value);
			span0_nodes.forEach(detach);
			a0_nodes.forEach(detach);
			t2 = claim_space(div0_nodes);

			a1 = claim_element(div0_nodes, "A", {
				class: true,
				href: true,
				"aria-label": true
			});

			var a1_nodes = children(a1);
			claim_component(icon1.$$.fragment, a1_nodes);
			t3 = claim_space(a1_nodes);
			span1 = claim_element(a1_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t4 = claim_text(span1_nodes, t4_value);
			span1_nodes.forEach(detach);
			a1_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t5 = claim_space(div3_nodes);
			header = claim_element(div3_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div1 = claim_element(header_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			nav0 = claim_element(div1_nodes, "NAV", { class: true });
			var nav0_nodes = children(nav0);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(nav0_nodes);
			}

			nav0_nodes.forEach(detach);
			t6 = claim_space(div1_nodes);
			a2 = claim_element(div1_nodes, "A", { href: true, class: true });
			var a2_nodes = children(a2);
			span2 = claim_element(a2_nodes, "SPAN", { class: true });
			var span2_nodes = children(span2);
			t7 = claim_text(span2_nodes, t7_value);
			span2_nodes.forEach(detach);
			t8 = claim_space(a2_nodes);
			img0 = claim_element(a2_nodes, "IMG", { src: true, alt: true });
			a2_nodes.forEach(detach);
			t9 = claim_space(div1_nodes);
			nav1 = claim_element(div1_nodes, "NAV", { class: true });
			var nav1_nodes = children(nav1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav1_nodes);
			}

			nav1_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t10 = claim_space(header_nodes);
			div2 = claim_element(header_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			a3 = claim_element(div2_nodes, "A", { href: true, class: true });
			var a3_nodes = children(a3);
			img1 = claim_element(a3_nodes, "IMG", { src: true, alt: true });
			a3_nodes.forEach(detach);
			t11 = claim_space(div2_nodes);

			button = claim_element(div2_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon2.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			t12 = claim_space(div2_nodes);
			if (if_block) if_block.l(div2_nodes);
			div2_nodes.forEach(detach);
			header_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "label svelte-6hkp3j");
			attr(a0, "class", "phone svelte-6hkp3j");
			attr(a0, "href", a0_href_value = "tel:" + /*contacts*/ ctx[2].phone);
			attr(a0, "aria-label", "Call");
			attr(span1, "class", "label svelte-6hkp3j");
			attr(a1, "class", "address svelte-6hkp3j");
			attr(a1, "href", a1_href_value = "maps:" + /*contacts*/ ctx[2].address);
			attr(a1, "aria-label", "Address");
			attr(div0, "class", "banner svelte-6hkp3j");
			attr(nav0, "class", "svelte-6hkp3j");
			attr(span2, "class", "sr-only");
			if (!src_url_equal(img0.src, img0_src_value = /*logo*/ ctx[0].url)) attr(img0, "src", img0_src_value);
			attr(img0, "alt", img0_alt_value = /*logo*/ ctx[0].alt);
			attr(a2, "href", "/");
			attr(a2, "class", "logo svelte-6hkp3j");
			attr(nav1, "class", "svelte-6hkp3j");
			attr(div1, "class", "desktop-nav svelte-6hkp3j");
			if (!src_url_equal(img1.src, img1_src_value = /*logo*/ ctx[0].url)) attr(img1, "src", img1_src_value);
			attr(img1, "alt", img1_alt_value = /*logo*/ ctx[0].alt);
			attr(a3, "href", "/");
			attr(a3, "class", "logo svelte-6hkp3j");
			attr(button, "id", "open");
			attr(button, "aria-label", "Open mobile navigation");
			attr(button, "class", "svelte-6hkp3j");
			attr(div2, "class", "mobile-nav svelte-6hkp3j");
			attr(header, "class", "section-container svelte-6hkp3j");
			attr(div3, "class", "section");
			attr(div3, "id", "section-b799c6e1");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div0);
			append_hydration(div0, a0);
			mount_component(icon0, a0, null);
			append_hydration(a0, t0);
			append_hydration(a0, span0);
			append_hydration(span0, t1);
			append_hydration(div0, t2);
			append_hydration(div0, a1);
			mount_component(icon1, a1, null);
			append_hydration(a1, t3);
			append_hydration(a1, span1);
			append_hydration(span1, t4);
			append_hydration(div3, t5);
			append_hydration(div3, header);
			append_hydration(header, div1);
			append_hydration(div1, nav0);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				if (each_blocks_1[i]) {
					each_blocks_1[i].m(nav0, null);
				}
			}

			append_hydration(div1, t6);
			append_hydration(div1, a2);
			append_hydration(a2, span2);
			append_hydration(span2, t7);
			append_hydration(a2, t8);
			append_hydration(a2, img0);
			append_hydration(div1, t9);
			append_hydration(div1, nav1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav1, null);
				}
			}

			append_hydration(header, t10);
			append_hydration(header, div2);
			append_hydration(div2, a3);
			append_hydration(a3, img1);
			append_hydration(div2, t11);
			append_hydration(div2, button);
			mount_component(icon2, button, null);
			append_hydration(div2, t12);
			if (if_block) if_block.m(div2, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[8]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if ((!current || dirty & /*contacts*/ 4) && t1_value !== (t1_value = /*contacts*/ ctx[2].phone + "")) set_data(t1, t1_value);

			if (!current || dirty & /*contacts*/ 4 && a0_href_value !== (a0_href_value = "tel:" + /*contacts*/ ctx[2].phone)) {
				attr(a0, "href", a0_href_value);
			}

			if ((!current || dirty & /*contacts*/ 4) && t4_value !== (t4_value = /*contacts*/ ctx[2].address + "")) set_data(t4, t4_value);

			if (!current || dirty & /*contacts*/ 4 && a1_href_value !== (a1_href_value = "maps:" + /*contacts*/ ctx[2].address)) {
				attr(a1, "href", a1_href_value);
			}

			if (dirty & /*site_nav, window*/ 2) {
				each_value_2 = /*site_nav*/ ctx[1].left;
				let i;

				for (i = 0; i < each_value_2.length; i += 1) {
					const child_ctx = get_each_context_2(ctx, each_value_2, i);

					if (each_blocks_1[i]) {
						each_blocks_1[i].p(child_ctx, dirty);
					} else {
						each_blocks_1[i] = create_each_block_2(child_ctx);
						each_blocks_1[i].c();
						each_blocks_1[i].m(nav0, null);
					}
				}

				for (; i < each_blocks_1.length; i += 1) {
					each_blocks_1[i].d(1);
				}

				each_blocks_1.length = each_value_2.length;
			}

			if ((!current || dirty & /*logo*/ 1) && t7_value !== (t7_value = /*logo*/ ctx[0].alt + "")) set_data(t7, t7_value);

			if (!current || dirty & /*logo*/ 1 && !src_url_equal(img0.src, img0_src_value = /*logo*/ ctx[0].url)) {
				attr(img0, "src", img0_src_value);
			}

			if (!current || dirty & /*logo*/ 1 && img0_alt_value !== (img0_alt_value = /*logo*/ ctx[0].alt)) {
				attr(img0, "alt", img0_alt_value);
			}

			if (dirty & /*site_nav, window*/ 2) {
				each_value_1 = /*site_nav*/ ctx[1].right;
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav1, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}

			if (!current || dirty & /*logo*/ 1 && !src_url_equal(img1.src, img1_src_value = /*logo*/ ctx[0].url)) {
				attr(img1, "src", img1_src_value);
			}

			if (!current || dirty & /*logo*/ 1 && img1_alt_value !== (img1_alt_value = /*logo*/ ctx[0].alt)) {
				attr(img1, "alt", img1_alt_value);
			}

			if (/*mobileNavOpen*/ ctx[3]) {
				if (if_block) {
					if_block.p(ctx, dirty);

					if (dirty & /*mobileNavOpen*/ 8) {
						transition_in(if_block, 1);
					}
				} else {
					if_block = create_if_block$1(ctx);
					if_block.c();
					transition_in(if_block, 1);
					if_block.m(div2, null);
				}
			} else if (if_block) {
				group_outros();

				transition_out(if_block, 1, 1, () => {
					if_block = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon0.$$.fragment, local);
			transition_in(icon1.$$.fragment, local);
			transition_in(icon2.$$.fragment, local);
			transition_in(if_block);
			current = true;
		},
		o(local) {
			transition_out(icon0.$$.fragment, local);
			transition_out(icon1.$$.fragment, local);
			transition_out(icon2.$$.fragment, local);
			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div3);
			destroy_component(icon0);
			destroy_component(icon1);
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
			destroy_component(icon2);
			if (if_block) if_block.d();
			mounted = false;
			dispose();
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let { social } = $$props;
	let { site_footer } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { contacts } = $$props;
	let mobileNavOpen = false;

	const click_handler = () => $$invalidate(3, mobileNavOpen = true);
	const click_handler_1 = () => $$invalidate(3, mobileNavOpen = false);

	$$self.$$set = $$props => {
		if ('social' in $$props) $$invalidate(4, social = $$props.social);
		if ('site_footer' in $$props) $$invalidate(5, site_footer = $$props.site_footer);
		if ('title' in $$props) $$invalidate(6, title = $$props.title);
		if ('description' in $$props) $$invalidate(7, description = $$props.description);
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(1, site_nav = $$props.site_nav);
		if ('contacts' in $$props) $$invalidate(2, contacts = $$props.contacts);
	};

	return [
		logo,
		site_nav,
		contacts,
		mobileNavOpen,
		social,
		site_footer,
		title,
		description,
		click_handler,
		click_handler_1
	];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$2, safe_not_equal, {
			social: 4,
			site_footer: 5,
			title: 6,
			description: 7,
			logo: 0,
			site_nav: 1,
			contacts: 2
		});
	}
}

/* generated by Svelte v3.59.1 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[6] = list[i];
	child_ctx[8] = i;
	return child_ctx;
}

// (116:6) {#each teasers as teaser, i}
function create_each_block$1(ctx) {
	let div3;
	let div0;
	let img;
	let img_src_value;
	let t0;
	let div2;
	let h3;
	let t1_value = /*teaser*/ ctx[6].title + "";
	let t1;
	let t2;
	let div1;
	let raw_value = /*teaser*/ ctx[6].description.html + "";
	let t3;

	return {
		c() {
			div3 = element("div");
			div0 = element("div");
			img = element("img");
			t0 = space();
			div2 = element("div");
			h3 = element("h3");
			t1 = text(t1_value);
			t2 = space();
			div1 = element("div");
			t3 = space();
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div0 = claim_element(div3_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			img = claim_element(div0_nodes, "IMG", { src: true, class: true });
			div0_nodes.forEach(detach);
			t0 = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			h3 = claim_element(div2_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t1 = claim_text(h3_nodes, t1_value);
			h3_nodes.forEach(detach);
			t2 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t3 = claim_space(div3_nodes);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*teaser*/ ctx[6].image.url)) attr(img, "src", img_src_value);
			attr(img, "class", "svelte-1ef0mlv");
			attr(div0, "class", "image");
			attr(h3, "class", "title svelte-1ef0mlv");
			attr(div1, "class", "description svelte-1ef0mlv");
			attr(div2, "class", "body");
			attr(div3, "class", "teaser svelte-1ef0mlv");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div0);
			append_hydration(div0, img);
			append_hydration(div3, t0);
			append_hydration(div3, div2);
			append_hydration(div2, h3);
			append_hydration(h3, t1);
			append_hydration(div2, t2);
			append_hydration(div2, div1);
			div1.innerHTML = raw_value;
			append_hydration(div3, t3);
		},
		p(ctx, dirty) {
			if (dirty & /*teasers*/ 2 && !src_url_equal(img.src, img_src_value = /*teaser*/ ctx[6].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*teasers*/ 2 && t1_value !== (t1_value = /*teaser*/ ctx[6].title + "")) set_data(t1, t1_value);
			if (dirty & /*teasers*/ 2 && raw_value !== (raw_value = /*teaser*/ ctx[6].description.html + "")) div1.innerHTML = raw_value;		},
		d(detaching) {
			if (detaching) detach(div3);
		}
	};
}

function create_fragment$3(ctx) {
	let div3;
	let section;
	let div2;
	let div0;
	let h2;
	let t0;
	let t1;
	let div1;
	let t2;
	let svg0;
	let path0;
	let t3;
	let svg1;
	let path1;
	let each_value = /*teasers*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	return {
		c() {
			div3 = element("div");
			section = element("section");
			div2 = element("div");
			div0 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			div1 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t2 = space();
			svg0 = svg_element("svg");
			path0 = svg_element("path");
			t3 = space();
			svg1 = svg_element("svg");
			path1 = svg_element("path");
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			section = claim_element(div3_nodes, "SECTION", {});
			var section_nodes = children(section);
			div2 = claim_element(section_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t1 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div1_nodes);
			}

			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t2 = claim_space(section_nodes);

			svg0 = claim_svg_element(section_nodes, "svg", {
				viewBox: true,
				fill: true,
				xmlns: true,
				class: true
			});

			var svg0_nodes = children(svg0);
			path0 = claim_svg_element(svg0_nodes, "path", { d: true, fill: true });
			children(path0).forEach(detach);
			svg0_nodes.forEach(detach);
			t3 = claim_space(section_nodes);

			svg1 = claim_svg_element(section_nodes, "svg", {
				viewBox: true,
				fill: true,
				xmlns: true,
				class: true
			});

			var svg1_nodes = children(svg1);
			path1 = claim_svg_element(svg1_nodes, "path", { d: true, fill: true });
			children(path1).forEach(detach);
			svg1_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading");
			attr(div0, "class", "header-section svelte-1ef0mlv");
			attr(div1, "class", "teasers svelte-1ef0mlv");
			attr(div2, "class", "section-container svelte-1ef0mlv");
			attr(path0, "d", "M0.499993 171C23.176 171 44.9233 161.992 60.9576 145.958C76.992 129.923 86 108.176 86 85.5C86 62.824 76.992 41.0767 60.9576 25.0424C44.9233 9.00801 23.176 6.7786e-07 0.500013 -3.73732e-06L0.499996 85.5L0.499993 171Z");
			attr(path0, "fill", "var(--color-shade)");
			attr(svg0, "viewBox", "0 0 86 171");
			attr(svg0, "fill", "none");
			attr(svg0, "xmlns", "http://www.w3.org/2000/svg");
			attr(svg0, "class", "svelte-1ef0mlv");
			attr(path1, "d", "M85.5 1.01958e-06C62.824 7.49169e-07 41.0767 9.00801 25.0424 25.0424C9.00801 41.0767 3.00198e-06 62.824 1.01958e-06 85.5C-9.62822e-07 108.176 9.00801 129.923 25.0424 145.958C41.0767 161.992 62.824 171 85.5 171L85.5 85.5L85.5 1.01958e-06Z");
			attr(path1, "fill", "var(--color-shade)");
			attr(svg1, "viewBox", "0 0 86 171");
			attr(svg1, "fill", "none");
			attr(svg1, "xmlns", "http://www.w3.org/2000/svg");
			attr(svg1, "class", "svelte-1ef0mlv");
			attr(div3, "class", "section");
			attr(div3, "id", "section-4afb18b6");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, section);
			append_hydration(section, div2);
			append_hydration(div2, div0);
			append_hydration(div0, h2);
			append_hydration(h2, t0);
			append_hydration(div2, t1);
			append_hydration(div2, div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div1, null);
				}
			}

			append_hydration(section, t2);
			append_hydration(section, svg0);
			append_hydration(svg0, path0);
			append_hydration(section, t3);
			append_hydration(section, svg1);
			append_hydration(svg1, path1);
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);

			if (dirty & /*teasers*/ 2) {
				each_value = /*teasers*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div1, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div3);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$3($$self, $$props, $$invalidate) {
	let { social } = $$props;
	let { site_footer } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { heading } = $$props;
	let { teasers } = $$props;

	$$self.$$set = $$props => {
		if ('social' in $$props) $$invalidate(2, social = $$props.social);
		if ('site_footer' in $$props) $$invalidate(3, site_footer = $$props.site_footer);
		if ('title' in $$props) $$invalidate(4, title = $$props.title);
		if ('description' in $$props) $$invalidate(5, description = $$props.description);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('teasers' in $$props) $$invalidate(1, teasers = $$props.teasers);
	};

	return [heading, teasers, social, site_footer, title, description];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			social: 2,
			site_footer: 3,
			title: 4,
			description: 5,
			heading: 0,
			teasers: 1
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$4(ctx) {
	let div1;
	let section;
	let div0;
	let h2;
	let t0;
	let t1;
	let h3;
	let t2;
	let t3;
	let a;
	let t4_value = /*link*/ ctx[2].label + "";
	let t4;
	let a_href_value;

	return {
		c() {
			div1 = element("div");
			section = element("section");
			div0 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			h3 = element("h3");
			t2 = text(/*subheading*/ ctx[1]);
			t3 = space();
			a = element("a");
			t4 = text(t4_value);
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			h3 = claim_element(div0_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t2 = claim_text(h3_nodes, /*subheading*/ ctx[1]);
			h3_nodes.forEach(detach);
			t3 = claim_space(div0_nodes);
			a = claim_element(div0_nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t4 = claim_text(a_nodes, t4_value);
			a_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-2borlu");
			attr(h3, "class", "subheading svelte-2borlu");
			attr(a, "class", "address button");
			attr(a, "href", a_href_value = /*link*/ ctx[2].url);
			attr(div0, "class", "section-container svelte-2borlu");
			attr(section, "class", "svelte-2borlu");
			attr(div1, "class", "section");
			attr(div1, "id", "section-1331b32e");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, section);
			append_hydration(section, div0);
			append_hydration(div0, h2);
			append_hydration(h2, t0);
			append_hydration(div0, t1);
			append_hydration(div0, h3);
			append_hydration(h3, t2);
			append_hydration(div0, t3);
			append_hydration(div0, a);
			append_hydration(a, t4);
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (dirty & /*subheading*/ 2) set_data(t2, /*subheading*/ ctx[1]);
			if (dirty & /*link*/ 4 && t4_value !== (t4_value = /*link*/ ctx[2].label + "")) set_data(t4, t4_value);

			if (dirty & /*link*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[2].url)) {
				attr(a, "href", a_href_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	let { social } = $$props;
	let { site_footer } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { heading } = $$props;
	let { subheading } = $$props;
	let { link } = $$props;

	$$self.$$set = $$props => {
		if ('social' in $$props) $$invalidate(3, social = $$props.social);
		if ('site_footer' in $$props) $$invalidate(4, site_footer = $$props.site_footer);
		if ('title' in $$props) $$invalidate(5, title = $$props.title);
		if ('description' in $$props) $$invalidate(6, description = $$props.description);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('subheading' in $$props) $$invalidate(1, subheading = $$props.subheading);
		if ('link' in $$props) $$invalidate(2, link = $$props.link);
	};

	return [heading, subheading, link, social, site_footer, title, description];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$4, create_fragment$4, safe_not_equal, {
			social: 3,
			site_footer: 4,
			title: 5,
			description: 6,
			heading: 0,
			subheading: 1,
			link: 2
		});
	}
}

/* generated by Svelte v3.59.1 */

function get_each_context$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[5] = list[i].link;
	child_ctx[6] = list[i].icon;
	return child_ctx;
}

function get_each_context_1$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[5] = list[i].link;
	return child_ctx;
}

// (87:4) {#each links as { link }}
function create_each_block_1$1(ctx) {
	let a;
	let t_value = /*link*/ ctx[5].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-s3xnx0");
			attr(a, "href", a_href_value = /*link*/ ctx[5].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*links*/ 2 && t_value !== (t_value = /*link*/ ctx[5].label + "")) set_data(t, t_value);

			if (dirty & /*links*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[5].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (93:4) {#each social as { link, icon }}
function create_each_block$2(ctx) {
	let a;
	let icon;
	let t;
	let a_href_value;
	let a_aria_label_value;
	let current;
	icon = new Component$1({ props: { icon: /*icon*/ ctx[6] } });

	return {
		c() {
			a = element("a");
			create_component(icon.$$.fragment);
			t = space();
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", {
				href: true,
				"aria-label": true,
				class: true
			});

			var a_nodes = children(a);
			claim_component(icon.$$.fragment, a_nodes);
			t = claim_space(a_nodes);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[5].url);
			attr(a, "aria-label", a_aria_label_value = /*link*/ ctx[5].label);
			attr(a, "class", "svelte-s3xnx0");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			mount_component(icon, a, null);
			append_hydration(a, t);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*social*/ 1) icon_changes.icon = /*icon*/ ctx[6];
			icon.$set(icon_changes);

			if (!current || dirty & /*social*/ 1 && a_href_value !== (a_href_value = /*link*/ ctx[5].url)) {
				attr(a, "href", a_href_value);
			}

			if (!current || dirty & /*social*/ 1 && a_aria_label_value !== (a_aria_label_value = /*link*/ ctx[5].label)) {
				attr(a, "aria-label", a_aria_label_value);
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
			if (detaching) detach(a);
			destroy_component(icon);
		}
	};
}

function create_fragment$5(ctx) {
	let div1;
	let footer;
	let nav;
	let t0;
	let span;
	let t1;
	let a;
	let t2;
	let t3;
	let div0;
	let current;
	let each_value_1 = /*links*/ ctx[1];
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks_1[i] = create_each_block_1$1(get_each_context_1$1(ctx, each_value_1, i));
	}

	let each_value = /*social*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$2(get_each_context$2(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div1 = element("div");
			footer = element("footer");
			nav = element("nav");

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t0 = space();
			span = element("span");
			t1 = text("Powered by ");
			a = element("a");
			t2 = text("Primo");
			t3 = space();
			div0 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			footer = claim_element(div1_nodes, "FOOTER", { class: true });
			var footer_nodes = children(footer);
			nav = claim_element(footer_nodes, "NAV", { class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(nav_nodes);
			}

			nav_nodes.forEach(detach);
			t0 = claim_space(footer_nodes);
			span = claim_element(footer_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t1 = claim_text(span_nodes, "Powered by ");
			a = claim_element(span_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t2 = claim_text(a_nodes, "Primo");
			a_nodes.forEach(detach);
			span_nodes.forEach(detach);
			t3 = claim_space(footer_nodes);
			div0 = claim_element(footer_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			footer_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(nav, "class", "svelte-s3xnx0");
			attr(a, "href", "https://primo.so");
			attr(a, "class", "svelte-s3xnx0");
			attr(span, "class", "primo svelte-s3xnx0");
			attr(div0, "class", "social-links svelte-s3xnx0");
			attr(footer, "class", "section-container svelte-s3xnx0");
			attr(div1, "class", "section");
			attr(div1, "id", "section-6d1d6d1e");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, footer);
			append_hydration(footer, nav);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				if (each_blocks_1[i]) {
					each_blocks_1[i].m(nav, null);
				}
			}

			append_hydration(footer, t0);
			append_hydration(footer, span);
			append_hydration(span, t1);
			append_hydration(span, a);
			append_hydration(a, t2);
			append_hydration(footer, t3);
			append_hydration(footer, div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div0, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (dirty & /*links*/ 2) {
				each_value_1 = /*links*/ ctx[1];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$1(ctx, each_value_1, i);

					if (each_blocks_1[i]) {
						each_blocks_1[i].p(child_ctx, dirty);
					} else {
						each_blocks_1[i] = create_each_block_1$1(child_ctx);
						each_blocks_1[i].c();
						each_blocks_1[i].m(nav, null);
					}
				}

				for (; i < each_blocks_1.length; i += 1) {
					each_blocks_1[i].d(1);
				}

				each_blocks_1.length = each_value_1.length;
			}

			if (dirty & /*social*/ 1) {
				each_value = /*social*/ ctx[0];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$2(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$2(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(div0, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	let { social } = $$props;
	let { site_footer } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { links } = $$props;

	$$self.$$set = $$props => {
		if ('social' in $$props) $$invalidate(0, social = $$props.social);
		if ('site_footer' in $$props) $$invalidate(2, site_footer = $$props.site_footer);
		if ('title' in $$props) $$invalidate(3, title = $$props.title);
		if ('description' in $$props) $$invalidate(4, description = $$props.description);
		if ('links' in $$props) $$invalidate(1, links = $$props.links);
	};

	return [social, links, site_footer, title, description];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, create_fragment$5, safe_not_equal, {
			social: 0,
			site_footer: 2,
			title: 3,
			description: 4,
			links: 1
		});
	}
}

/* generated by Svelte v3.59.1 */

function instance$6($$self, $$props, $$invalidate) {
	let { social } = $$props;
	let { site_footer } = $$props;
	let { title } = $$props;
	let { description } = $$props;

	$$self.$$set = $$props => {
		if ('social' in $$props) $$invalidate(0, social = $$props.social);
		if ('site_footer' in $$props) $$invalidate(1, site_footer = $$props.site_footer);
		if ('title' in $$props) $$invalidate(2, title = $$props.title);
		if ('description' in $$props) $$invalidate(3, description = $$props.description);
	};

	return [social, site_footer, title, description];
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$6, null, safe_not_equal, {
			social: 0,
			site_footer: 1,
			title: 2,
			description: 3
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$6(ctx) {
	let component_0;
	let t0;
	let component_1;
	let t1;
	let component_2;
	let t2;
	let component_3;
	let t3;
	let component_4;
	let t4;
	let component_5;
	let current;

	component_0 = new Component({
			props: {
				social: [
					{
						"icon": "mdi:instagram",
						"link": {
							"url": "http://instagram.com",
							"label": "Instagram"
						}
					},
					{
						"icon": "mdi:facebook",
						"link": {
							"url": "https://facebook.com",
							"label": "Facebook"
						}
					}
				],
				site_footer: [
					{
						"link": { "url": "/about", "label": "About" }
					},
					{
						"link": { "url": "/contact", "label": "Contact" }
					}
				],
				title: "Menu",
				description: ""
			}
		});

	component_1 = new Component$2({
			props: {
				social: [
					{
						"icon": "mdi:instagram",
						"link": {
							"url": "http://instagram.com",
							"label": "Instagram"
						}
					},
					{
						"icon": "mdi:facebook",
						"link": {
							"url": "https://facebook.com",
							"label": "Facebook"
						}
					}
				],
				site_footer: [
					{
						"link": { "url": "/about", "label": "About" }
					},
					{
						"link": { "url": "/contact", "label": "Contact" }
					}
				],
				title: "Menu",
				description: "",
				logo: {
					"alt": "",
					"src": "data:image/svg+xml,%3Csvg id='logo-74' viewBox='0 0 70 44' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M65.5268 5.40852C65.5268 5.45982 65.5268 5.52395 65.5137 5.56243C65.4481 6.06264 65.4481 6.56285 65.4874 7.07589C65.5137 7.20415 65.5399 7.33241 65.6449 7.43502C65.8154 7.6274 66.0777 7.58893 66.1827 7.35806C66.2352 7.24263 66.2352 7.12719 66.2089 7.01176C66.0777 6.52437 66.0515 6.01134 66.0384 5.51112C66.0384 5.48547 66.0384 5.44699 66.0384 5.40852C66.1827 5.39569 66.3139 5.38286 66.4319 5.38286C66.5238 5.37004 66.6025 5.35721 66.6681 5.31873C66.8648 5.21613 66.8648 4.99809 66.6549 4.89548C66.5762 4.857 66.4713 4.84417 66.3795 4.84417C66.0515 4.857 65.7236 4.857 65.3956 4.857C65.2776 4.857 65.1595 4.86983 65.0414 4.88265C64.9758 4.89548 64.8971 4.89548 64.8447 4.93396C64.7528 4.97243 64.7004 5.03656 64.7004 5.12634C64.7135 5.21613 64.7528 5.26743 64.8447 5.30591C64.8971 5.34439 64.9627 5.35721 65.0283 5.35721C65.1857 5.37004 65.3563 5.39569 65.5268 5.40852ZM69.1342 5.99851C69.1342 6.01134 69.1473 6.02416 69.1473 6.02416C69.1998 6.37046 69.2523 6.70394 69.2916 7.03741C69.3048 7.15284 69.3179 7.25545 69.3966 7.34523C69.5671 7.56327 69.8295 7.53762 69.9475 7.30676C70 7.19132 70.0131 7.07589 69.9869 6.94763C69.9082 6.56285 69.8688 6.17807 69.7901 5.80612C69.7376 5.57525 69.6721 5.35721 69.6065 5.152C69.5671 5.02374 69.4753 4.93395 69.3179 4.92113C69.1605 4.89548 69.0424 4.97243 68.9768 5.08787C68.8981 5.19047 68.8325 5.29308 68.78 5.40852C68.6882 5.61373 68.6095 5.81895 68.5046 6.01134C68.4914 6.06264 68.4783 6.10112 68.4521 6.13959C68.439 6.11394 68.4259 6.10112 68.4259 6.10112C68.2553 5.78047 68.0979 5.45982 67.9274 5.152C67.9011 5.12634 67.888 5.10069 67.8749 5.07504C67.7962 4.95961 67.7044 4.89548 67.5601 4.89548C67.4289 4.9083 67.3239 4.98526 67.2584 5.10069C67.2321 5.152 67.2321 5.19047 67.219 5.24178C67.1665 5.65221 67.1009 6.06264 67.0485 6.47307C67.0222 6.70394 67.0091 6.9348 67.0091 7.16567C66.996 7.21697 67.0091 7.2811 67.0353 7.33241C67.0616 7.43501 67.1403 7.49915 67.2452 7.51197C67.3764 7.5248 67.4682 7.48632 67.5076 7.38371C67.5469 7.30676 67.5601 7.24263 67.5732 7.1785C67.6257 6.94763 67.665 6.72959 67.7044 6.51155C67.7306 6.38329 67.7437 6.28068 67.7831 6.13959C67.8093 6.1909 67.8355 6.22938 67.8618 6.26785C67.9798 6.42177 68.0979 6.57568 68.2422 6.70394C68.3865 6.80654 68.5046 6.79372 68.6226 6.67828C68.6489 6.65263 68.662 6.63981 68.6882 6.61415C68.8063 6.43459 68.9506 6.25503 69.0686 6.07546C69.0949 6.04981 69.108 6.02416 69.1342 5.99851Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M38.9087 5.6605C38.8175 5.90425 38.8001 6.07986 38.8422 6.22582C38.8887 6.4243 39.0094 6.48928 39.1732 6.4388C40.714 6.06627 44.0927 7.12367 45.3436 7.41838C45.6386 7.48026 45.8786 7.10791 45.6773 6.77407C45.3835 6.45077 42.0063 5.0666 40.7177 4.99113C40.2126 4.96322 39.3096 4.83658 38.9087 5.6605Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.1133 1.17982C52.2775 1.27249 52.3693 1.36089 52.4146 1.45966C52.4821 1.58922 52.4465 1.67886 52.3331 1.7246C51.3146 2.21062 49.9593 4.30303 49.4122 5.02468C49.2796 5.19069 48.9737 5.09422 48.9275 4.82122C48.937 4.51254 50.1384 2.24181 50.8089 1.62334C51.0724 1.38187 51.5077 0.908078 52.1133 1.17982Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M44.0023 0.149796C44.1996 0.00441887 44.4046 -0.0465256 44.5093 0.0479512C46.046 1.3329 46.8609 3.36773 47.3655 5.23057C47.3845 5.27397 47.3857 5.33625 47.3705 5.40122C47.3642 5.45675 47.3227 5.51541 47.2568 5.5608C47.1864 5.61091 47.1258 5.62617 47.0973 5.58299C46.4238 4.68732 42.5771 1.20242 44.0023 0.149796Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M11.461 22.4276C11.8293 22.1595 12.2297 21.9363 12.6534 21.7631C13.0967 21.6392 13.5692 21.6597 13.9995 21.8217C14.4297 21.9837 14.7944 22.2782 15.0382 22.6608C15.2563 23.0424 15.3416 23.483 15.2814 23.9162C15.2212 24.3493 15.0187 24.7516 14.7043 25.0625C14.4606 25.3145 14.1839 25.534 13.8816 25.7154C12.5342 26.5665 11.1748 27.3709 9.81547 28.222C9.53732 28.435 9.24225 28.6261 8.93308 28.7933C8.46281 29.0226 7.92537 29.084 7.41368 28.9669C6.902 28.8499 6.44826 28.5616 6.13092 28.1521C5.89369 27.8621 5.69348 27.545 5.53471 27.2077C4.24691 24.5612 2.91142 21.9263 1.67131 19.2331C1.09895 18.0673 0.633913 16.7265 0.180798 15.4324C-0.0152406 15.0564 -0.0535225 14.6205 0.0741037 14.2173C0.20173 13.8141 0.485195 13.4755 0.864201 13.2735C1.24321 13.0715 1.68785 13.0221 2.10357 13.1357C2.51929 13.2493 2.87329 13.517 3.09027 13.8818C3.75722 14.7484 4.34761 15.6689 4.85504 16.6333C6.14284 18.965 7.37103 21.2967 8.61113 23.5585C8.68334 23.6835 8.76296 23.8041 8.84961 23.9199C9.783 23.5362 10.6609 23.0345 11.461 22.4276Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M24.7761 21.6142C21.8309 24.9835 16.8943 24.1324 14.4141 19.7954C12.6493 16.7175 12.3393 11.6343 16.1789 8.42817C16.9988 7.75694 17.9792 7.29969 19.0287 7.09907C20.3155 6.9187 21.6277 7.14066 22.7777 7.73324C23.9277 8.32582 24.8567 9.25867 25.432 10.3985C27.5306 14.1293 27.2325 18.886 24.7761 21.6142ZM23.5837 13.7562C23.2708 12.8394 22.6431 12.0567 21.807 11.541C21.3339 11.2113 20.759 11.051 20.1792 11.0871C19.5993 11.1232 19.0499 11.3535 18.6233 11.7392C16.9182 13.2199 16.5604 16.7292 17.8005 18.8161C17.9586 19.1564 18.1907 19.4588 18.4808 19.7022C18.7709 19.9456 19.1119 20.1241 19.4799 20.2251C19.8479 20.3262 20.234 20.3474 20.6113 20.2873C20.9886 20.2271 21.3478 20.0871 21.664 19.877C22.5883 19.1763 23.2664 18.2115 23.604 17.1167C23.9417 16.0218 23.9221 14.8513 23.548 13.7679L23.5837 13.7562Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M36.7955 15.2252C36.494 15.2886 36.1825 15.2924 35.8794 15.2363C35.5764 15.1802 35.2878 15.0655 35.0308 14.8988C34.8059 14.773 34.6123 14.6001 34.4639 14.3924C34.3156 14.1847 34.2162 13.9475 34.1729 13.6977C34.1295 13.448 34.1434 13.192 34.2133 12.9481C34.2833 12.7042 34.4078 12.4785 34.5777 12.2872C34.8737 11.9028 35.2939 11.6276 35.7701 11.5061C37.0134 11.1533 38.2933 10.9382 39.5858 10.8649C39.8698 10.8326 40.1575 10.8561 40.432 10.934C40.7066 11.012 40.9624 11.1427 41.1846 11.3187C41.4067 11.4946 41.5907 11.7122 41.7257 11.9586C41.8606 12.205 41.9439 12.4753 41.9706 12.7536C42.3432 14.1206 42.384 15.5539 42.0898 16.9391C41.0167 21.416 37.3202 22.9549 33.1706 21.5209C32.0058 21.1375 30.9845 20.4231 30.2373 19.469C29.2407 18.32 28.5341 16.9583 28.1744 15.4934C27.883 14.1889 27.9149 12.8353 28.2676 11.5454C28.6202 10.2555 29.2833 9.06675 30.2015 8.07845C31.0729 7.00428 32.2039 6.15891 33.4926 5.61846C34.3069 5.17961 35.2598 5.05483 36.1636 5.2687C36.3686 5.32418 36.5547 5.43228 36.7026 5.58179C36.8505 5.73131 36.9548 5.91678 37.0047 6.11899C37.0546 6.32119 37.0482 6.53276 36.9863 6.73176C36.9243 6.93075 36.8091 7.10992 36.6525 7.25068C36.3547 7.51423 36.0312 7.74853 35.6866 7.9502C34.6265 8.61027 33.704 9.46082 32.9679 10.4568C32.4854 11.1013 32.1531 11.8414 31.9945 12.6249C31.8358 13.4084 31.8547 14.2164 32.0498 14.9921C32.3202 16.0497 32.9203 16.999 33.7668 17.7085C36.3901 20.0403 39.8004 17.7901 39.2042 14.6073C38.3338 14.8172 37.5706 15.0387 36.7955 15.2252Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.8217 21.8007C48.9464 24.1325 44.5345 21.8007 43.5686 16.9041C42.8651 13.4065 44.2006 8.50982 48.8749 6.64443C49.8694 6.25608 50.9481 6.11973 52.0109 6.24803C53.2878 6.47658 54.4592 7.09121 55.3598 8.00528C56.2604 8.91934 56.845 10.0867 57.0309 11.3429C57.8179 15.505 56.0293 19.947 52.8217 21.8007ZM54.1692 13.9544C54.168 12.9859 53.8176 12.0487 53.1795 11.3079C52.8384 10.8497 52.3453 10.5214 51.7843 10.3789C51.2232 10.2365 50.6291 10.2887 50.103 10.5268C48.0044 11.4128 46.5258 14.6306 47.0624 16.9974C47.1034 17.3688 47.2268 17.727 47.4241 18.0469C47.6214 18.3668 47.8878 18.6407 48.2047 18.8495C48.5215 19.0582 48.8812 19.1968 49.2585 19.2555C49.6359 19.3141 50.0218 19.2915 50.3892 19.1892C51.4985 18.8103 52.459 18.1022 53.1366 17.1637C53.8143 16.2252 54.1753 15.1032 54.1692 13.9544Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M60.9499 22.7801C60.8914 23.2068 60.662 23.5933 60.312 23.8546C59.962 24.1158 59.5202 24.2305 59.0838 24.1733C58.6474 24.1161 58.2521 23.8917 57.9849 23.5495C57.7176 23.2074 57.6004 22.7754 57.6589 22.3487C57.7174 21.922 57.9469 21.5355 58.2968 21.2742C58.6468 21.0129 59.0886 20.8983 59.525 20.9555C59.9614 21.0127 60.3567 21.237 60.624 21.5792C60.8912 21.9214 61.0085 22.3534 60.9499 22.7801ZM59.9125 7.05247C60.1393 6.71382 60.472 6.45593 60.861 6.31726C61.2499 6.17859 61.6743 6.16657 62.0708 6.283C62.4739 6.38161 62.83 6.61262 63.0797 6.93735C63.3293 7.26209 63.4572 7.66082 63.4421 8.06678C63.3895 8.71795 63.2899 9.36468 63.144 10.0021C62.7505 12.159 62.3689 14.3158 61.9516 16.4494C61.7608 17.3005 61.5104 18.1166 61.2361 18.9793C61.1407 19.249 60.9813 19.4927 60.7711 19.6905C60.6404 19.8393 60.4735 19.9534 60.2857 20.0223C60.0979 20.0913 59.8954 20.1128 59.6969 20.0849C59.4984 20.057 59.3102 19.9806 59.1499 19.8628C58.9896 19.7449 58.8623 19.5894 58.7798 19.4107C58.638 19.0901 58.561 18.7456 58.5532 18.3964C58.5532 16.9507 58.5532 15.4934 58.6486 14.036C58.8107 11.9562 59.1295 9.89088 59.6025 7.85692C59.6582 7.58442 59.7631 7.32383 59.9125 7.08745V7.05247Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M6.42311 32.1488C6.28232 32.4561 6.24371 32.7987 6.31251 33.1284C6.35828 33.563 6.45881 33.9905 6.61181 34.4011C6.80283 34.9039 7.01658 35.4011 7.28014 36.0139C7.34075 36.1549 7.40409 36.3021 7.47037 36.457C7.82579 37.2872 8.27175 38.3482 8.8666 39.8837C9.03497 40.3199 9.18448 40.7597 9.33504 41.2025C9.39586 41.3814 9.4569 41.5609 9.51938 41.7408C9.74334 42.3804 10.1287 42.955 10.6395 43.4104C10.8564 43.6607 11.1441 43.8431 11.4667 43.9343C11.7956 44.0273 12.1454 44.0214 12.4708 43.9174C12.7962 43.8133 13.082 43.6159 13.2911 43.3508C13.4961 43.0909 13.618 42.7777 13.6417 42.4505C13.7747 41.8131 13.7293 41.1522 13.5101 40.5377C13.1622 39.5174 12.7659 38.4956 12.3089 37.4962L12.3068 37.4918C11.555 35.9282 10.7908 34.3754 9.99044 32.822L9.98445 32.8111C9.75015 32.4064 9.44566 32.0446 9.08466 31.742C8.8503 31.4719 8.52703 31.2897 8.17003 31.2269C7.80542 31.1628 7.42938 31.2274 7.10904 31.4093C6.806 31.5785 6.56578 31.8374 6.42311 32.1488Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M17.9057 28.2986C16.7269 28.0001 15.4958 27.9566 14.2982 28.1712C13.3706 28.2605 12.4583 28.4697 11.8248 28.8841C11.5026 29.095 11.2421 29.3658 11.0972 29.71C10.9515 30.0561 10.9329 30.4519 11.0523 30.8929C11.2703 31.7007 11.5534 32.4861 11.8355 33.269L11.8812 33.3958L11.8823 33.3986C12.7317 35.673 13.5892 37.9397 14.4545 40.1986C14.5554 40.5546 14.6981 40.898 14.8797 41.2219L14.8831 41.2279C15.123 41.6303 15.4307 41.9902 15.7932 42.2925C15.9745 42.4587 16.1987 42.5737 16.4418 42.6251C16.6873 42.6769 16.9426 42.6619 17.1799 42.5815C17.4173 42.5012 17.6275 42.3587 17.7877 42.1695C17.9453 41.9834 18.0485 41.7592 18.0864 41.5206C18.2428 40.8724 18.1927 40.1929 17.9427 39.5733C17.8647 39.3648 17.8035 39.1517 17.739 38.9274C17.7175 38.8526 17.6957 38.7765 17.6727 38.699C19.6534 37.942 21.7609 36.9241 22.502 34.5561C22.7922 33.7378 22.8164 32.8517 22.5712 32.0193C22.3258 31.186 21.8223 30.4474 21.1301 29.9052C20.188 29.1462 19.0875 28.5978 17.9057 28.2986ZM14.6382 31.2031C14.6772 31.1921 14.7165 31.1819 14.7559 31.1724C16.0454 30.9742 17.3647 31.2383 18.4709 31.9159C18.9584 32.2474 19.1581 32.6157 19.1924 32.9701C19.2278 33.335 19.0921 33.7304 18.8195 34.1105C18.3044 34.8285 17.3644 35.4032 16.5153 35.5103C15.8963 34.1165 15.2677 32.6663 14.6382 31.2031Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M25.7646 25.7473C27.1684 25.1134 28.9073 25.0039 30.268 25.4496C30.6107 25.5472 30.908 25.7583 31.1091 26.0468C31.3089 26.3335 31.4011 26.679 31.3703 27.0244C31.3683 27.2486 31.312 27.4692 31.2061 27.6682C31.0983 27.8708 30.9422 28.045 30.751 28.1762C30.5598 28.3073 30.3391 28.3916 30.1076 28.4217C29.876 28.4519 29.6405 28.4271 29.4208 28.3494L29.4041 28.3435L29.3884 28.3354C29.276 28.2779 29.1566 28.2346 29.0331 28.2064L29.0253 28.2047C28.0681 27.9561 27.1652 28.368 26.8354 28.8741C26.6781 29.1154 26.6586 29.359 26.7896 29.5806C26.9299 29.8179 27.274 30.0842 27.9703 30.274C28.1618 30.3254 28.3581 30.375 28.5572 30.4254C29.1078 30.5648 29.68 30.7096 30.2333 30.9103L30.2354 30.9111C32.788 31.8607 33.7385 33.8274 33.4131 35.6772C33.0912 37.5065 31.5287 39.1713 29.179 39.564C28.324 39.7493 27.4342 39.7132 26.5977 39.4593C25.7591 39.2046 25.0032 38.7399 24.4051 38.1111L24.3895 38.0947C24.2007 37.8578 24.0737 37.5795 24.0174 37.2842C23.9656 37.0177 23.9929 36.7423 24.0959 36.4904C24.1983 36.24 24.3715 36.0233 24.595 35.8654C24.8311 35.6864 25.1157 35.579 25.4136 35.5566C25.7105 35.5343 26.0076 35.5974 26.2683 35.738C26.5287 35.861 26.7709 36.0179 26.9883 36.2045L26.9924 36.2079C27.377 36.5518 27.8423 36.6414 28.2885 36.5584C28.7412 36.4742 29.1669 36.2123 29.4407 35.8648C29.7127 35.5195 29.8219 35.1093 29.6923 34.7111C29.5619 34.31 29.1698 33.8606 28.3083 33.4849C28.0831 33.3914 27.8496 33.316 27.6067 33.2426C27.5412 33.2228 27.4746 33.2031 27.4072 33.1831C27.2276 33.1298 27.0428 33.0749 26.8616 33.0144C26.7368 32.9728 26.613 32.9334 26.4904 32.8943C26.1553 32.7876 25.8286 32.6836 25.5142 32.5441C24.8299 32.3163 24.2387 31.8789 23.8286 31.2966C23.4168 30.712 23.2096 30.0129 23.2378 29.3037C23.24 27.5754 24.3533 26.3847 25.7646 25.7473Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M43.5619 25.5632C43.2897 25.4332 42.9887 25.3715 42.6861 25.3836C42.3834 25.3958 42.0886 25.4814 41.8283 25.6329C41.5696 25.7833 41.353 25.9939 41.1978 26.246C41.0555 26.4583 40.957 26.6957 40.9079 26.945C40.8588 27.1941 40.86 27.4501 40.9113 27.6986C40.962 28.018 41.0182 28.3286 41.0737 28.6349C41.1656 29.1418 41.255 29.6373 41.314 30.1425L41.3162 30.1553C41.4505 30.9476 41.5208 31.7489 41.5271 32.5519L41.5277 32.5633C41.5736 33.4305 41.2714 34.2808 40.6859 34.9338L40.6766 34.9454C40.4861 35.1841 40.2314 35.3663 39.9409 35.4716C39.6505 35.5769 39.3359 35.6011 39.0322 35.5415C38.7285 35.4819 38.4478 35.3409 38.2214 35.1342C37.995 34.9275 37.8317 34.6625 37.7502 34.3704C37.5762 33.7547 37.4755 33.1214 37.4499 32.4832L37.7471 27.8569C37.7515 27.7965 37.7565 27.7345 37.7616 27.6719C37.7729 27.5314 37.7845 27.3883 37.7893 27.2548C37.7963 27.0584 37.7903 26.8564 37.7435 26.6652C37.6956 26.4698 37.6045 26.2839 37.4429 26.1256C37.2829 25.9689 37.0669 25.8533 36.7951 25.7746C36.3036 25.6355 35.888 25.6399 35.5417 25.7836C35.1952 25.9273 34.9578 26.1941 34.7898 26.5023C34.6231 26.8079 34.516 27.1697 34.435 27.5321C34.3749 27.801 34.3266 28.0833 34.2807 28.352C34.2648 28.4446 34.2493 28.5355 34.2336 28.6238L34.2332 28.6264C33.9876 30.1 33.9145 31.5962 34.0153 33.086C34.0341 33.8911 34.2058 34.6858 34.5218 35.4295C34.8783 36.3891 35.524 37.2205 36.3737 37.814C37.2252 38.4087 38.2413 38.7364 39.2875 38.7537C40.3337 38.771 41.3606 38.4771 42.2322 37.911C43.1024 37.3457 43.7768 36.5355 44.1662 35.5876C44.7109 34.3801 44.9667 33.0669 44.9139 31.7481C44.8819 30.7853 44.8283 29.8151 44.775 28.8498C44.7488 28.3763 44.7227 27.9038 44.6993 27.4342C44.6875 26.9633 44.5287 26.5072 44.2441 26.1271C44.068 25.8868 43.8336 25.693 43.5619 25.5632Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M53.1961 32.8173C53.1685 32.8516 53.1394 32.8871 53.109 32.924C52.8876 31.6752 52.6824 30.4268 52.4769 29.1765C52.4032 28.7279 52.3291 28.2774 52.2546 27.8282L52.2462 27.7781L52.219 27.7348C52.1677 27.6533 52.1626 27.5734 52.1626 27.403V27.3833L52.1595 27.3638C52.1039 27.0119 51.9411 26.6844 51.6924 26.4242C51.4444 26.1647 51.1223 25.9841 50.768 25.9057C50.4143 25.8204 50.0426 25.8392 49.6997 25.9598C49.3577 26.0801 49.0596 26.2963 48.8426 26.5813C48.6622 26.8 48.5143 27.0426 48.4035 27.3018C48.152 27.8602 47.8983 28.42 47.6439 28.9813L47.6395 28.991C47.0044 30.3923 46.365 31.803 45.7442 33.2248L45.7423 33.2294C45.3612 34.1513 45.0466 35.1227 44.7331 36.0911C44.6705 36.2844 44.6079 36.4776 44.5448 36.6703C44.4316 36.9759 44.3821 37.3005 44.3991 37.625C44.3785 37.9155 44.4496 38.2053 44.603 38.4552C44.7594 38.7102 44.9937 38.9108 45.2728 39.0289C45.5686 39.1557 45.8993 39.1826 46.2126 39.1054C46.5252 39.0283 46.8028 38.8519 47.0017 38.6039C47.2557 38.2984 47.4742 37.9652 47.6524 37.6122C48.1783 36.5604 48.6809 35.4958 49.1812 34.4358C49.3748 34.0258 49.5629 33.6586 49.7769 33.2587C49.7916 33.308 49.8066 33.3561 49.8221 33.4043C50.0464 34.3698 50.425 35.2946 50.9439 36.1448C51.0421 36.3249 51.1789 36.4823 51.3449 36.6062C51.5129 36.7316 51.7068 36.8196 51.9131 36.8643C52.1194 36.909 52.3332 36.9092 52.5396 36.8649C52.7457 36.8207 52.9402 36.7326 53.1083 36.6078L53.441 36.3643L56.0233 34.2376L55.8706 35.1891C55.661 36.497 55.453 37.794 55.232 39.0913C55.0874 39.6663 55.0876 40.2669 55.2326 40.8417C55.2954 41.1652 55.4554 41.463 55.6922 41.6972C55.931 41.9333 56.2368 42.0937 56.57 42.1577C56.9032 42.2216 57.2484 42.1862 57.5607 42.0559C57.8685 41.9276 58.1303 41.713 58.3133 41.4395C58.7391 40.923 59.0041 40.2977 59.0769 39.638C59.1865 38.7064 59.3103 37.7621 59.4342 36.8181C59.5769 35.73 59.7196 34.6422 59.8401 33.5753L59.8405 33.572C59.9565 32.4041 60.0126 31.2314 60.0087 30.058C60.0341 29.6872 59.9397 29.3178 59.7385 29.0021C59.5366 28.6853 59.2376 28.439 58.8842 28.2981C58.5166 28.1347 58.1051 28.091 57.7102 28.1736C57.3179 28.2556 56.9628 28.4578 56.6964 28.7507C56.2201 29.1814 55.7733 29.6423 55.3588 30.1304L55.356 30.1337C54.9035 30.685 54.4541 31.2471 54.0076 31.8056C53.7361 32.1451 53.4654 32.4838 53.1961 32.8173Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3C/svg%3E",
					"url": "data:image/svg+xml,%3Csvg id='logo-74' viewBox='0 0 70 44' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M65.5268 5.40852C65.5268 5.45982 65.5268 5.52395 65.5137 5.56243C65.4481 6.06264 65.4481 6.56285 65.4874 7.07589C65.5137 7.20415 65.5399 7.33241 65.6449 7.43502C65.8154 7.6274 66.0777 7.58893 66.1827 7.35806C66.2352 7.24263 66.2352 7.12719 66.2089 7.01176C66.0777 6.52437 66.0515 6.01134 66.0384 5.51112C66.0384 5.48547 66.0384 5.44699 66.0384 5.40852C66.1827 5.39569 66.3139 5.38286 66.4319 5.38286C66.5238 5.37004 66.6025 5.35721 66.6681 5.31873C66.8648 5.21613 66.8648 4.99809 66.6549 4.89548C66.5762 4.857 66.4713 4.84417 66.3795 4.84417C66.0515 4.857 65.7236 4.857 65.3956 4.857C65.2776 4.857 65.1595 4.86983 65.0414 4.88265C64.9758 4.89548 64.8971 4.89548 64.8447 4.93396C64.7528 4.97243 64.7004 5.03656 64.7004 5.12634C64.7135 5.21613 64.7528 5.26743 64.8447 5.30591C64.8971 5.34439 64.9627 5.35721 65.0283 5.35721C65.1857 5.37004 65.3563 5.39569 65.5268 5.40852ZM69.1342 5.99851C69.1342 6.01134 69.1473 6.02416 69.1473 6.02416C69.1998 6.37046 69.2523 6.70394 69.2916 7.03741C69.3048 7.15284 69.3179 7.25545 69.3966 7.34523C69.5671 7.56327 69.8295 7.53762 69.9475 7.30676C70 7.19132 70.0131 7.07589 69.9869 6.94763C69.9082 6.56285 69.8688 6.17807 69.7901 5.80612C69.7376 5.57525 69.6721 5.35721 69.6065 5.152C69.5671 5.02374 69.4753 4.93395 69.3179 4.92113C69.1605 4.89548 69.0424 4.97243 68.9768 5.08787C68.8981 5.19047 68.8325 5.29308 68.78 5.40852C68.6882 5.61373 68.6095 5.81895 68.5046 6.01134C68.4914 6.06264 68.4783 6.10112 68.4521 6.13959C68.439 6.11394 68.4259 6.10112 68.4259 6.10112C68.2553 5.78047 68.0979 5.45982 67.9274 5.152C67.9011 5.12634 67.888 5.10069 67.8749 5.07504C67.7962 4.95961 67.7044 4.89548 67.5601 4.89548C67.4289 4.9083 67.3239 4.98526 67.2584 5.10069C67.2321 5.152 67.2321 5.19047 67.219 5.24178C67.1665 5.65221 67.1009 6.06264 67.0485 6.47307C67.0222 6.70394 67.0091 6.9348 67.0091 7.16567C66.996 7.21697 67.0091 7.2811 67.0353 7.33241C67.0616 7.43501 67.1403 7.49915 67.2452 7.51197C67.3764 7.5248 67.4682 7.48632 67.5076 7.38371C67.5469 7.30676 67.5601 7.24263 67.5732 7.1785C67.6257 6.94763 67.665 6.72959 67.7044 6.51155C67.7306 6.38329 67.7437 6.28068 67.7831 6.13959C67.8093 6.1909 67.8355 6.22938 67.8618 6.26785C67.9798 6.42177 68.0979 6.57568 68.2422 6.70394C68.3865 6.80654 68.5046 6.79372 68.6226 6.67828C68.6489 6.65263 68.662 6.63981 68.6882 6.61415C68.8063 6.43459 68.9506 6.25503 69.0686 6.07546C69.0949 6.04981 69.108 6.02416 69.1342 5.99851Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M38.9087 5.6605C38.8175 5.90425 38.8001 6.07986 38.8422 6.22582C38.8887 6.4243 39.0094 6.48928 39.1732 6.4388C40.714 6.06627 44.0927 7.12367 45.3436 7.41838C45.6386 7.48026 45.8786 7.10791 45.6773 6.77407C45.3835 6.45077 42.0063 5.0666 40.7177 4.99113C40.2126 4.96322 39.3096 4.83658 38.9087 5.6605Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.1133 1.17982C52.2775 1.27249 52.3693 1.36089 52.4146 1.45966C52.4821 1.58922 52.4465 1.67886 52.3331 1.7246C51.3146 2.21062 49.9593 4.30303 49.4122 5.02468C49.2796 5.19069 48.9737 5.09422 48.9275 4.82122C48.937 4.51254 50.1384 2.24181 50.8089 1.62334C51.0724 1.38187 51.5077 0.908078 52.1133 1.17982Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M44.0023 0.149796C44.1996 0.00441887 44.4046 -0.0465256 44.5093 0.0479512C46.046 1.3329 46.8609 3.36773 47.3655 5.23057C47.3845 5.27397 47.3857 5.33625 47.3705 5.40122C47.3642 5.45675 47.3227 5.51541 47.2568 5.5608C47.1864 5.61091 47.1258 5.62617 47.0973 5.58299C46.4238 4.68732 42.5771 1.20242 44.0023 0.149796Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M11.461 22.4276C11.8293 22.1595 12.2297 21.9363 12.6534 21.7631C13.0967 21.6392 13.5692 21.6597 13.9995 21.8217C14.4297 21.9837 14.7944 22.2782 15.0382 22.6608C15.2563 23.0424 15.3416 23.483 15.2814 23.9162C15.2212 24.3493 15.0187 24.7516 14.7043 25.0625C14.4606 25.3145 14.1839 25.534 13.8816 25.7154C12.5342 26.5665 11.1748 27.3709 9.81547 28.222C9.53732 28.435 9.24225 28.6261 8.93308 28.7933C8.46281 29.0226 7.92537 29.084 7.41368 28.9669C6.902 28.8499 6.44826 28.5616 6.13092 28.1521C5.89369 27.8621 5.69348 27.545 5.53471 27.2077C4.24691 24.5612 2.91142 21.9263 1.67131 19.2331C1.09895 18.0673 0.633913 16.7265 0.180798 15.4324C-0.0152406 15.0564 -0.0535225 14.6205 0.0741037 14.2173C0.20173 13.8141 0.485195 13.4755 0.864201 13.2735C1.24321 13.0715 1.68785 13.0221 2.10357 13.1357C2.51929 13.2493 2.87329 13.517 3.09027 13.8818C3.75722 14.7484 4.34761 15.6689 4.85504 16.6333C6.14284 18.965 7.37103 21.2967 8.61113 23.5585C8.68334 23.6835 8.76296 23.8041 8.84961 23.9199C9.783 23.5362 10.6609 23.0345 11.461 22.4276Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M24.7761 21.6142C21.8309 24.9835 16.8943 24.1324 14.4141 19.7954C12.6493 16.7175 12.3393 11.6343 16.1789 8.42817C16.9988 7.75694 17.9792 7.29969 19.0287 7.09907C20.3155 6.9187 21.6277 7.14066 22.7777 7.73324C23.9277 8.32582 24.8567 9.25867 25.432 10.3985C27.5306 14.1293 27.2325 18.886 24.7761 21.6142ZM23.5837 13.7562C23.2708 12.8394 22.6431 12.0567 21.807 11.541C21.3339 11.2113 20.759 11.051 20.1792 11.0871C19.5993 11.1232 19.0499 11.3535 18.6233 11.7392C16.9182 13.2199 16.5604 16.7292 17.8005 18.8161C17.9586 19.1564 18.1907 19.4588 18.4808 19.7022C18.7709 19.9456 19.1119 20.1241 19.4799 20.2251C19.8479 20.3262 20.234 20.3474 20.6113 20.2873C20.9886 20.2271 21.3478 20.0871 21.664 19.877C22.5883 19.1763 23.2664 18.2115 23.604 17.1167C23.9417 16.0218 23.9221 14.8513 23.548 13.7679L23.5837 13.7562Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M36.7955 15.2252C36.494 15.2886 36.1825 15.2924 35.8794 15.2363C35.5764 15.1802 35.2878 15.0655 35.0308 14.8988C34.8059 14.773 34.6123 14.6001 34.4639 14.3924C34.3156 14.1847 34.2162 13.9475 34.1729 13.6977C34.1295 13.448 34.1434 13.192 34.2133 12.9481C34.2833 12.7042 34.4078 12.4785 34.5777 12.2872C34.8737 11.9028 35.2939 11.6276 35.7701 11.5061C37.0134 11.1533 38.2933 10.9382 39.5858 10.8649C39.8698 10.8326 40.1575 10.8561 40.432 10.934C40.7066 11.012 40.9624 11.1427 41.1846 11.3187C41.4067 11.4946 41.5907 11.7122 41.7257 11.9586C41.8606 12.205 41.9439 12.4753 41.9706 12.7536C42.3432 14.1206 42.384 15.5539 42.0898 16.9391C41.0167 21.416 37.3202 22.9549 33.1706 21.5209C32.0058 21.1375 30.9845 20.4231 30.2373 19.469C29.2407 18.32 28.5341 16.9583 28.1744 15.4934C27.883 14.1889 27.9149 12.8353 28.2676 11.5454C28.6202 10.2555 29.2833 9.06675 30.2015 8.07845C31.0729 7.00428 32.2039 6.15891 33.4926 5.61846C34.3069 5.17961 35.2598 5.05483 36.1636 5.2687C36.3686 5.32418 36.5547 5.43228 36.7026 5.58179C36.8505 5.73131 36.9548 5.91678 37.0047 6.11899C37.0546 6.32119 37.0482 6.53276 36.9863 6.73176C36.9243 6.93075 36.8091 7.10992 36.6525 7.25068C36.3547 7.51423 36.0312 7.74853 35.6866 7.9502C34.6265 8.61027 33.704 9.46082 32.9679 10.4568C32.4854 11.1013 32.1531 11.8414 31.9945 12.6249C31.8358 13.4084 31.8547 14.2164 32.0498 14.9921C32.3202 16.0497 32.9203 16.999 33.7668 17.7085C36.3901 20.0403 39.8004 17.7901 39.2042 14.6073C38.3338 14.8172 37.5706 15.0387 36.7955 15.2252Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.8217 21.8007C48.9464 24.1325 44.5345 21.8007 43.5686 16.9041C42.8651 13.4065 44.2006 8.50982 48.8749 6.64443C49.8694 6.25608 50.9481 6.11973 52.0109 6.24803C53.2878 6.47658 54.4592 7.09121 55.3598 8.00528C56.2604 8.91934 56.845 10.0867 57.0309 11.3429C57.8179 15.505 56.0293 19.947 52.8217 21.8007ZM54.1692 13.9544C54.168 12.9859 53.8176 12.0487 53.1795 11.3079C52.8384 10.8497 52.3453 10.5214 51.7843 10.3789C51.2232 10.2365 50.6291 10.2887 50.103 10.5268C48.0044 11.4128 46.5258 14.6306 47.0624 16.9974C47.1034 17.3688 47.2268 17.727 47.4241 18.0469C47.6214 18.3668 47.8878 18.6407 48.2047 18.8495C48.5215 19.0582 48.8812 19.1968 49.2585 19.2555C49.6359 19.3141 50.0218 19.2915 50.3892 19.1892C51.4985 18.8103 52.459 18.1022 53.1366 17.1637C53.8143 16.2252 54.1753 15.1032 54.1692 13.9544Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M60.9499 22.7801C60.8914 23.2068 60.662 23.5933 60.312 23.8546C59.962 24.1158 59.5202 24.2305 59.0838 24.1733C58.6474 24.1161 58.2521 23.8917 57.9849 23.5495C57.7176 23.2074 57.6004 22.7754 57.6589 22.3487C57.7174 21.922 57.9469 21.5355 58.2968 21.2742C58.6468 21.0129 59.0886 20.8983 59.525 20.9555C59.9614 21.0127 60.3567 21.237 60.624 21.5792C60.8912 21.9214 61.0085 22.3534 60.9499 22.7801ZM59.9125 7.05247C60.1393 6.71382 60.472 6.45593 60.861 6.31726C61.2499 6.17859 61.6743 6.16657 62.0708 6.283C62.4739 6.38161 62.83 6.61262 63.0797 6.93735C63.3293 7.26209 63.4572 7.66082 63.4421 8.06678C63.3895 8.71795 63.2899 9.36468 63.144 10.0021C62.7505 12.159 62.3689 14.3158 61.9516 16.4494C61.7608 17.3005 61.5104 18.1166 61.2361 18.9793C61.1407 19.249 60.9813 19.4927 60.7711 19.6905C60.6404 19.8393 60.4735 19.9534 60.2857 20.0223C60.0979 20.0913 59.8954 20.1128 59.6969 20.0849C59.4984 20.057 59.3102 19.9806 59.1499 19.8628C58.9896 19.7449 58.8623 19.5894 58.7798 19.4107C58.638 19.0901 58.561 18.7456 58.5532 18.3964C58.5532 16.9507 58.5532 15.4934 58.6486 14.036C58.8107 11.9562 59.1295 9.89088 59.6025 7.85692C59.6582 7.58442 59.7631 7.32383 59.9125 7.08745V7.05247Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M6.42311 32.1488C6.28232 32.4561 6.24371 32.7987 6.31251 33.1284C6.35828 33.563 6.45881 33.9905 6.61181 34.4011C6.80283 34.9039 7.01658 35.4011 7.28014 36.0139C7.34075 36.1549 7.40409 36.3021 7.47037 36.457C7.82579 37.2872 8.27175 38.3482 8.8666 39.8837C9.03497 40.3199 9.18448 40.7597 9.33504 41.2025C9.39586 41.3814 9.4569 41.5609 9.51938 41.7408C9.74334 42.3804 10.1287 42.955 10.6395 43.4104C10.8564 43.6607 11.1441 43.8431 11.4667 43.9343C11.7956 44.0273 12.1454 44.0214 12.4708 43.9174C12.7962 43.8133 13.082 43.6159 13.2911 43.3508C13.4961 43.0909 13.618 42.7777 13.6417 42.4505C13.7747 41.8131 13.7293 41.1522 13.5101 40.5377C13.1622 39.5174 12.7659 38.4956 12.3089 37.4962L12.3068 37.4918C11.555 35.9282 10.7908 34.3754 9.99044 32.822L9.98445 32.8111C9.75015 32.4064 9.44566 32.0446 9.08466 31.742C8.8503 31.4719 8.52703 31.2897 8.17003 31.2269C7.80542 31.1628 7.42938 31.2274 7.10904 31.4093C6.806 31.5785 6.56578 31.8374 6.42311 32.1488Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M17.9057 28.2986C16.7269 28.0001 15.4958 27.9566 14.2982 28.1712C13.3706 28.2605 12.4583 28.4697 11.8248 28.8841C11.5026 29.095 11.2421 29.3658 11.0972 29.71C10.9515 30.0561 10.9329 30.4519 11.0523 30.8929C11.2703 31.7007 11.5534 32.4861 11.8355 33.269L11.8812 33.3958L11.8823 33.3986C12.7317 35.673 13.5892 37.9397 14.4545 40.1986C14.5554 40.5546 14.6981 40.898 14.8797 41.2219L14.8831 41.2279C15.123 41.6303 15.4307 41.9902 15.7932 42.2925C15.9745 42.4587 16.1987 42.5737 16.4418 42.6251C16.6873 42.6769 16.9426 42.6619 17.1799 42.5815C17.4173 42.5012 17.6275 42.3587 17.7877 42.1695C17.9453 41.9834 18.0485 41.7592 18.0864 41.5206C18.2428 40.8724 18.1927 40.1929 17.9427 39.5733C17.8647 39.3648 17.8035 39.1517 17.739 38.9274C17.7175 38.8526 17.6957 38.7765 17.6727 38.699C19.6534 37.942 21.7609 36.9241 22.502 34.5561C22.7922 33.7378 22.8164 32.8517 22.5712 32.0193C22.3258 31.186 21.8223 30.4474 21.1301 29.9052C20.188 29.1462 19.0875 28.5978 17.9057 28.2986ZM14.6382 31.2031C14.6772 31.1921 14.7165 31.1819 14.7559 31.1724C16.0454 30.9742 17.3647 31.2383 18.4709 31.9159C18.9584 32.2474 19.1581 32.6157 19.1924 32.9701C19.2278 33.335 19.0921 33.7304 18.8195 34.1105C18.3044 34.8285 17.3644 35.4032 16.5153 35.5103C15.8963 34.1165 15.2677 32.6663 14.6382 31.2031Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M25.7646 25.7473C27.1684 25.1134 28.9073 25.0039 30.268 25.4496C30.6107 25.5472 30.908 25.7583 31.1091 26.0468C31.3089 26.3335 31.4011 26.679 31.3703 27.0244C31.3683 27.2486 31.312 27.4692 31.2061 27.6682C31.0983 27.8708 30.9422 28.045 30.751 28.1762C30.5598 28.3073 30.3391 28.3916 30.1076 28.4217C29.876 28.4519 29.6405 28.4271 29.4208 28.3494L29.4041 28.3435L29.3884 28.3354C29.276 28.2779 29.1566 28.2346 29.0331 28.2064L29.0253 28.2047C28.0681 27.9561 27.1652 28.368 26.8354 28.8741C26.6781 29.1154 26.6586 29.359 26.7896 29.5806C26.9299 29.8179 27.274 30.0842 27.9703 30.274C28.1618 30.3254 28.3581 30.375 28.5572 30.4254C29.1078 30.5648 29.68 30.7096 30.2333 30.9103L30.2354 30.9111C32.788 31.8607 33.7385 33.8274 33.4131 35.6772C33.0912 37.5065 31.5287 39.1713 29.179 39.564C28.324 39.7493 27.4342 39.7132 26.5977 39.4593C25.7591 39.2046 25.0032 38.7399 24.4051 38.1111L24.3895 38.0947C24.2007 37.8578 24.0737 37.5795 24.0174 37.2842C23.9656 37.0177 23.9929 36.7423 24.0959 36.4904C24.1983 36.24 24.3715 36.0233 24.595 35.8654C24.8311 35.6864 25.1157 35.579 25.4136 35.5566C25.7105 35.5343 26.0076 35.5974 26.2683 35.738C26.5287 35.861 26.7709 36.0179 26.9883 36.2045L26.9924 36.2079C27.377 36.5518 27.8423 36.6414 28.2885 36.5584C28.7412 36.4742 29.1669 36.2123 29.4407 35.8648C29.7127 35.5195 29.8219 35.1093 29.6923 34.7111C29.5619 34.31 29.1698 33.8606 28.3083 33.4849C28.0831 33.3914 27.8496 33.316 27.6067 33.2426C27.5412 33.2228 27.4746 33.2031 27.4072 33.1831C27.2276 33.1298 27.0428 33.0749 26.8616 33.0144C26.7368 32.9728 26.613 32.9334 26.4904 32.8943C26.1553 32.7876 25.8286 32.6836 25.5142 32.5441C24.8299 32.3163 24.2387 31.8789 23.8286 31.2966C23.4168 30.712 23.2096 30.0129 23.2378 29.3037C23.24 27.5754 24.3533 26.3847 25.7646 25.7473Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M43.5619 25.5632C43.2897 25.4332 42.9887 25.3715 42.6861 25.3836C42.3834 25.3958 42.0886 25.4814 41.8283 25.6329C41.5696 25.7833 41.353 25.9939 41.1978 26.246C41.0555 26.4583 40.957 26.6957 40.9079 26.945C40.8588 27.1941 40.86 27.4501 40.9113 27.6986C40.962 28.018 41.0182 28.3286 41.0737 28.6349C41.1656 29.1418 41.255 29.6373 41.314 30.1425L41.3162 30.1553C41.4505 30.9476 41.5208 31.7489 41.5271 32.5519L41.5277 32.5633C41.5736 33.4305 41.2714 34.2808 40.6859 34.9338L40.6766 34.9454C40.4861 35.1841 40.2314 35.3663 39.9409 35.4716C39.6505 35.5769 39.3359 35.6011 39.0322 35.5415C38.7285 35.4819 38.4478 35.3409 38.2214 35.1342C37.995 34.9275 37.8317 34.6625 37.7502 34.3704C37.5762 33.7547 37.4755 33.1214 37.4499 32.4832L37.7471 27.8569C37.7515 27.7965 37.7565 27.7345 37.7616 27.6719C37.7729 27.5314 37.7845 27.3883 37.7893 27.2548C37.7963 27.0584 37.7903 26.8564 37.7435 26.6652C37.6956 26.4698 37.6045 26.2839 37.4429 26.1256C37.2829 25.9689 37.0669 25.8533 36.7951 25.7746C36.3036 25.6355 35.888 25.6399 35.5417 25.7836C35.1952 25.9273 34.9578 26.1941 34.7898 26.5023C34.6231 26.8079 34.516 27.1697 34.435 27.5321C34.3749 27.801 34.3266 28.0833 34.2807 28.352C34.2648 28.4446 34.2493 28.5355 34.2336 28.6238L34.2332 28.6264C33.9876 30.1 33.9145 31.5962 34.0153 33.086C34.0341 33.8911 34.2058 34.6858 34.5218 35.4295C34.8783 36.3891 35.524 37.2205 36.3737 37.814C37.2252 38.4087 38.2413 38.7364 39.2875 38.7537C40.3337 38.771 41.3606 38.4771 42.2322 37.911C43.1024 37.3457 43.7768 36.5355 44.1662 35.5876C44.7109 34.3801 44.9667 33.0669 44.9139 31.7481C44.8819 30.7853 44.8283 29.8151 44.775 28.8498C44.7488 28.3763 44.7227 27.9038 44.6993 27.4342C44.6875 26.9633 44.5287 26.5072 44.2441 26.1271C44.068 25.8868 43.8336 25.693 43.5619 25.5632Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3Cpath class='ccustom' d='M53.1961 32.8173C53.1685 32.8516 53.1394 32.8871 53.109 32.924C52.8876 31.6752 52.6824 30.4268 52.4769 29.1765C52.4032 28.7279 52.3291 28.2774 52.2546 27.8282L52.2462 27.7781L52.219 27.7348C52.1677 27.6533 52.1626 27.5734 52.1626 27.403V27.3833L52.1595 27.3638C52.1039 27.0119 51.9411 26.6844 51.6924 26.4242C51.4444 26.1647 51.1223 25.9841 50.768 25.9057C50.4143 25.8204 50.0426 25.8392 49.6997 25.9598C49.3577 26.0801 49.0596 26.2963 48.8426 26.5813C48.6622 26.8 48.5143 27.0426 48.4035 27.3018C48.152 27.8602 47.8983 28.42 47.6439 28.9813L47.6395 28.991C47.0044 30.3923 46.365 31.803 45.7442 33.2248L45.7423 33.2294C45.3612 34.1513 45.0466 35.1227 44.7331 36.0911C44.6705 36.2844 44.6079 36.4776 44.5448 36.6703C44.4316 36.9759 44.3821 37.3005 44.3991 37.625C44.3785 37.9155 44.4496 38.2053 44.603 38.4552C44.7594 38.7102 44.9937 38.9108 45.2728 39.0289C45.5686 39.1557 45.8993 39.1826 46.2126 39.1054C46.5252 39.0283 46.8028 38.8519 47.0017 38.6039C47.2557 38.2984 47.4742 37.9652 47.6524 37.6122C48.1783 36.5604 48.6809 35.4958 49.1812 34.4358C49.3748 34.0258 49.5629 33.6586 49.7769 33.2587C49.7916 33.308 49.8066 33.3561 49.8221 33.4043C50.0464 34.3698 50.425 35.2946 50.9439 36.1448C51.0421 36.3249 51.1789 36.4823 51.3449 36.6062C51.5129 36.7316 51.7068 36.8196 51.9131 36.8643C52.1194 36.909 52.3332 36.9092 52.5396 36.8649C52.7457 36.8207 52.9402 36.7326 53.1083 36.6078L53.441 36.3643L56.0233 34.2376L55.8706 35.1891C55.661 36.497 55.453 37.794 55.232 39.0913C55.0874 39.6663 55.0876 40.2669 55.2326 40.8417C55.2954 41.1652 55.4554 41.463 55.6922 41.6972C55.931 41.9333 56.2368 42.0937 56.57 42.1577C56.9032 42.2216 57.2484 42.1862 57.5607 42.0559C57.8685 41.9276 58.1303 41.713 58.3133 41.4395C58.7391 40.923 59.0041 40.2977 59.0769 39.638C59.1865 38.7064 59.3103 37.7621 59.4342 36.8181C59.5769 35.73 59.7196 34.6422 59.8401 33.5753L59.8405 33.572C59.9565 32.4041 60.0126 31.2314 60.0087 30.058C60.0341 29.6872 59.9397 29.3178 59.7385 29.0021C59.5366 28.6853 59.2376 28.439 58.8842 28.2981C58.5166 28.1347 58.1051 28.091 57.7102 28.1736C57.3179 28.2556 56.9628 28.4578 56.6964 28.7507C56.2201 29.1814 55.7733 29.6423 55.3588 30.1304L55.356 30.1337C54.9035 30.685 54.4541 31.2471 54.0076 31.8056C53.7361 32.1451 53.4654 32.4838 53.1961 32.8173Z' fill='%23716996' stop-color='%23716996'%3E%3C/path%3E%3C/svg%3E",
					"size": null
				},
				site_nav: {
					"left": [{ "link": { "url": "/", "label": "Menu" } }],
					"right": [{ "link": { "url": "/", "label": "About" } }]
				},
				contacts: {
					"phone": "381-393-1203",
					"address": "New York, New York"
				}
			}
		});

	component_2 = new Component$3({
			props: {
				social: [
					{
						"icon": "mdi:instagram",
						"link": {
							"url": "http://instagram.com",
							"label": "Instagram"
						}
					},
					{
						"icon": "mdi:facebook",
						"link": {
							"url": "https://facebook.com",
							"label": "Facebook"
						}
					}
				],
				site_footer: [
					{
						"link": { "url": "/about", "label": "About" }
					},
					{
						"link": { "url": "/contact", "label": "Contact" }
					}
				],
				title: "Menu",
				description: "",
				heading: "Store Menu",
				teasers: [
					{
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1528919460073-af8ef5efad10?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=2149&q=80",
							"url": "https://images.unsplash.com/photo-1528919460073-af8ef5efad10?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=2149&q=80",
							"size": null
						},
						"title": "Assorted Macaroons ",
						"description": "<p>25 flavors of macaroons including pistachio, strawberry short-cake, vanilla, and others.</p>"
					},
					{
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1624353365286-3f8d62daad51?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=2070&q=80",
							"url": "https://images.unsplash.com/photo-1624353365286-3f8d62daad51?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=2070&q=80",
							"size": null
						},
						"title": "Gourmet Brownie",
						"description": "<p>A richly dense pile of chocolate with a dollop of heavy whipping cream. You won't be able to share this one.</p>"
					}
				]
			}
		});

	component_3 = new Component$4({
			props: {
				social: [
					{
						"icon": "mdi:instagram",
						"link": {
							"url": "http://instagram.com",
							"label": "Instagram"
						}
					},
					{
						"icon": "mdi:facebook",
						"link": {
							"url": "https://facebook.com",
							"label": "Facebook"
						}
					}
				],
				site_footer: [
					{
						"link": { "url": "/about", "label": "About" }
					},
					{
						"link": { "url": "/contact", "label": "Contact" }
					}
				],
				title: "Menu",
				description: "",
				heading: "Interested in catering your next event?",
				subheading: "We cater for birthdays, weddings, and other special occasions.",
				link: {
					"url": "/contact",
					"label": "Get in touch"
				}
			}
		});

	component_4 = new Component$5({
			props: {
				social: [],
				site_footer: [
					{
						"link": { "url": "/about", "label": "About" }
					},
					{
						"link": { "url": "/contact", "label": "Contact" }
					}
				],
				title: "Menu",
				description: "",
				links: []
			}
		});

	component_5 = new Component$6({
			props: {
				social: [
					{
						"icon": "mdi:instagram",
						"link": {
							"url": "http://instagram.com",
							"label": "Instagram"
						}
					},
					{
						"icon": "mdi:facebook",
						"link": {
							"url": "https://facebook.com",
							"label": "Facebook"
						}
					}
				],
				site_footer: [
					{
						"link": { "url": "/about", "label": "About" }
					},
					{
						"link": { "url": "/contact", "label": "Contact" }
					}
				],
				title: "Menu",
				description: ""
			}
		});

	return {
		c() {
			create_component(component_0.$$.fragment);
			t0 = space();
			create_component(component_1.$$.fragment);
			t1 = space();
			create_component(component_2.$$.fragment);
			t2 = space();
			create_component(component_3.$$.fragment);
			t3 = space();
			create_component(component_4.$$.fragment);
			t4 = space();
			create_component(component_5.$$.fragment);
		},
		l(nodes) {
			claim_component(component_0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(component_1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(component_2.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(component_3.$$.fragment, nodes);
			t3 = claim_space(nodes);
			claim_component(component_4.$$.fragment, nodes);
			t4 = claim_space(nodes);
			claim_component(component_5.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(component_0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(component_1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(component_2, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(component_3, target, anchor);
			insert_hydration(target, t3, anchor);
			mount_component(component_4, target, anchor);
			insert_hydration(target, t4, anchor);
			mount_component(component_5, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(component_0.$$.fragment, local);
			transition_in(component_1.$$.fragment, local);
			transition_in(component_2.$$.fragment, local);
			transition_in(component_3.$$.fragment, local);
			transition_in(component_4.$$.fragment, local);
			transition_in(component_5.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			transition_out(component_5.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(component_0, detaching);
			if (detaching) detach(t0);
			destroy_component(component_1, detaching);
			if (detaching) detach(t1);
			destroy_component(component_2, detaching);
			if (detaching) detach(t2);
			destroy_component(component_3, detaching);
			if (detaching) detach(t3);
			destroy_component(component_4, detaching);
			if (detaching) detach(t4);
			destroy_component(component_5, detaching);
		}
	};
}

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$6, safe_not_equal, {});
	}
}

export default Component$7;
