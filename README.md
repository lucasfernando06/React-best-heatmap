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
    value: 1,
    valueLabel: 'Custom content...'
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
| `startDate`             | `Date`             | `Today's date`                                    | Yes       | Initial date                              |  
| `values`                | `array`            | `[]`                                              | Yes       | Custom values                             |
| `showWeekDays`          | `array`            | `[1,3,5]`                                         | Yes       | Showing days of week (0 - 6)              |    
| `showBlockTooltip`           | `bool`             | `true`                                            | No        | Show block tooltip                          |
| `showLegendTooltip`           | `bool`             | `true`                                            | No        | Show legend tooltip                          |
| `showMonths`            | `bool`             | `true`                                            | No        | Show months |                             |
| `locale`                | `string`           | `en`                                              | No        | Select the language (en/pt-br/es/fr)      |  
| `rangeDays`                | `number`            | `365`       | No        | Limit of days from start date                         | 
| `boxShape`              | `string`           | `square`                                          | No        | Select box shape (square/circle)          | 
| `legend`   | `array`   | `[...array]`                                       | Yes        | Legend array, check the proptypes to see the structure                    |  
| `contentBeforeLegend`   | `string/Element`   | `undefined`                                       | No        | Content before legend                     |  
| `contentAfterLegend`    | `string/Element`   | `undefined`                                       | No        | Content before legend                     |                             
                                        
### Check proptypes

```js
{
  startDate: PropTypes.instanceOf(Date).isRequired,
  values: PropTypes.array,
  showWeekDays: PropTypes.array,
  showBlockTooltip: PropTypes.bool,
  showLegendTooltip: PropTypes.bool,
  showMonths: PropTypes.bool,
  locale: PropTypes.string,
  rangeDays: PropTypes.number,
  boxShape: PropTypes.string,
  legend: PropTypes.arrayOf(PropTypes.shape({
    isInRange: PropTypes.func.isRequired, // Example: (value) => value > 3
    color: PropTypes.string.isRequired,
    label: PropTypes.string.isRequired,
  })),
  contentBeforeLegend: PropTypes.string,
  contentAfterLegend: PropTypes.string,
}
```

## Donate

If you liked, you can donate to support it :)

[![paypal](https://www.paypalobjects.com/en_US/i/btn/btn_donateCC_LG.gif)](https://www.paypal.com/donate?hosted_button_id=A2PGCFBMK59NL)