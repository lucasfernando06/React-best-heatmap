# React Best Heatmap 🚀

<p>Build and customize an heatmap for exactly what you need 🔥<p> 
  
<img src="https://www.dropbox.com/s/udqevegy0pv14co/heatmap.png?raw=1" />
  
### Usage

Simple and easy to get started.

```js
import React from 'react';
import HeatMap from 'react-best-heatmap';

const values = [
  {
    date: new Date(),
    count: 1
  }
];

const App = () => (
  <HeatMap values={values} />
);

export default App;
```
  
### Props
  
| Name                    | Type               | Default Value                                     | Required? | Description                               |
| ----------------------- | ------------------ | ------------------------------------------------- | --------- | ----------------------------------------  |
| `showWeekDays`          | `array`            | `[1,3,5]`                                         | Yes       | Showing days of week (0 - 6)              |     
| `startDate`             | `Date`             | `Today's date`                                    | Yes       | Initial date                              |  
| `values`                | `array`            | `[]`                                              | Yes       | Custom values                             |
| `showTooltip`           | `bool`             | `true`                                            | No        | Show box tooltip                          |
| `showMonths`            | `bool`             | `true`                                            | No        | Show months |                             |
| `legend`                | `array`            | `["#9BE9A8","#40C463","#30A14E","#216E39"]`       | No        | Select box colors                         | 
| `locale`                | `string`           | `en`                                              | No        | Select the language (en/pt-br/es/fr)      |  
| `boxShape`              | `string`           | `square`                                          | No        | Select box shape (square/circle)          |  
| `contentBeforeLegend`   | `string/Element`   | `undefined`                                       | No        | Content before legend                     |  
| `contentAfterLegend`    | `string/Element`   | `undefined`                                       | No        | Content before legend                     |                             
                                        
### Check proptypes

```js
{
  props: {
  showWeekDays: PropTypes.array,
  startDate: PropTypes.instanceOf(Date),
  values: PropTypes.array,
  showTooltip: PropTypes.bool,
  showMonths: PropTypes.bool,
  legend: PropTypes.array,
  locale: PropTypes.string,
  boxShape: PropTypes.string,
  contentBeforeLegend: PropTypes.string,
  contentAfterLegend: PropTypes.string,
}
```

## Donate

If you liked, you can donate to support it :)

[![paypal](https://www.paypalobjects.com/en_US/i/btn/btn_donateCC_LG.gif)](https://www.paypal.com/donate?hosted_button_id=A2PGCFBMK59NL)