# Isla web interface

## Installation/Build

Running `make` should be sufficient to build the web inferface
provided that rust/cargo are installed for the server, and
[npm](https://www.npmjs.com) is available for the client.

The client will be built by

1. Installing all the dependencies (locally) via `npm install`.
3. Transcompiling the javascript source code using `npm run build`.

There is also a `npm run deploy` command which minifys the javascript
and css source for deployment.

`main.bundle.js` and `style.bundle.css` will be located at `./client/dist/`.  If
`deploy` command is used, a `.js.gz` and `.css.gz` are also available.
Otherwise if `build` is used, a `.map` version of the files are available for
debugging purposes.

## Browser Support

Isla's UI is transcompiled from TypeScript to JS ECMAScript 5 (2009).
It is (hopefully) supported by all the following browser versions.

| Browser       | Version | From Date |
|---------------|:-------:|-----------|
| Chrome        | 23      | Sep 2012  |
| Firefox       | 21      | Apr 2013  |
| IE            | 9       | Mar 2011  |
| IE / Edge     | 10      | Sep 2012  |
| Safari        | 6       | Jul 2012  |
| Opera         | 15      | Jul 2013  |


## JS Libraries

Most of the UI is written in [TypeScript](https://www.typescriptlang.org), but
it also depends on the following JS libraries (see `package.json`):

- [GoldenLayout](http://golden-layout.com): A tab layout manager.
- [CodeMirror](https://codemirror.net): A text editor.
- [jQuery](https://jquery.com): A DOM traversal library.
- [lodash](https://lodash.com): It extends JS with useful utility functions.
- [viz.js](https://github.com/mdaines/viz.js): It provides a simple wrapper for
  using Graphviz in the browser. It is the *heaviest* Isla UI dependency.
- [webpack.js](https://webpack.js.org): A static module bundler. It also
  minize/unglify the files. This is a dev dependency only. It uses the
  following plugins:
  * [css-loader](https://github.com/webpack-contrib/css-loader): It allows
    webpack to load CSS.
  * [style-loader](https://github.com/webpack-contrib/style-loader): It is used
    as a fallback in case of `css-loader` errors.
  * [ts-loader](https://github.com/TypeStrong/ts-loader): TypeScript loader for
    webpack.
  * [compression-webpack-plugin](https://github.com/webpack-contrib/compression-webpack-plugin):
    It compress JS and CSS bundles with gzip.
  * [extract-text-webpack-plugin](https://github.com/webpack-contrib/extract-text-webpack-plugin):
    It bundles CSS separately, allowing the client to visualise the page before
    the JS files are loaded.
