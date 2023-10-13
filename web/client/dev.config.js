const Path = require('path');
const MiniCssExtractPlugin = require('mini-css-extract-plugin');

module.exports = {
  mode: 'development',
  devtool: 'source-map',
  entry: './src/index.ts',
  output: {
    devtoolModuleFilenameTemplate: '[absolute-resource-path]',
    filename: '[name].bundle.js',
    path: Path.resolve(__dirname, 'dist')
  },
  externals: [
    'fs'
  ],
  resolve: {
    extensions: [".ts", ".js"]
  },
  plugins: [ new MiniCssExtractPlugin() ],
  module: {
    rules: [{
      test: /\.tsx?$/,
      use: 'ts-loader',
      exclude: [/node_modules/, /tests/]
    },{
      test: /\.css$/,
      use: [ MiniCssExtractPlugin.loader, 'css-loader' ],
      sideEffects: true,
    }]
  },
};
