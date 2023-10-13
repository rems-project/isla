const Path = require('path');
const MiniCssExtractPlugin = require('mini-css-extract-plugin');

module.exports = {
  entry: './src/index.ts',
  mode: 'production',
  output: {
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
      use: [ MiniCssExtractPlugin.loader ]
    }]
  },
};
