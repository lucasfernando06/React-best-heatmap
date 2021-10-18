import React, { useState } from 'react';
import { addDays, differenceInDays, format, getDay, isSameDay } from 'date-fns';
import localeEN from 'date-fns/esm/locale/en-US';
import localeES from 'date-fns/esm/locale/es';
import localePT from 'date-fns/esm/locale/pt-BR';
import localeFR from 'date-fns/esm/locale/fr';

import Box from './Box';
import Column from './Column';
import {
  Container,
  ColumnsContainer,
  FlexContainer,
  WeekContainer,
  WeekLabel,
  BoxContainer
} from './styles';

const Heatmap = ({
  startDate,
  values,
  showWeekDays,
  legendColors,
  showTooltip,
  showMonths,
  locale,
  rangeDays,
  boxShape,
  contentBeforeLegend,
  contentAfterLegend
}) => {

  const getLocale = () => {
    if (locale === 'pt-br') return localePT;
    else if (locale === 'es') return localeES;
    else if (locale === 'fr') return localeFR;

    return localeEN;
  }

  const getValue = (refDate) => values?.find(x => isSameDay(x.date, refDate));

  const getStartDay = () => getDay(startDate);

  const getColumns = () => {
    const endDate = addDays(startDate, rangeDays);

    const startDay = getStartDay();

    const daysCount = differenceInDays(endDate, startDate);
    const columnsCount = Math.floor(daysCount / 7) + (startDay > 0 ? 1 : 0);

    const daysList = Array(daysCount).fill(0).map((_, index) => {
      const newDate = addDays(startDate, index);
      const value = getValue(newDate);

      return {
        date: new Date(newDate.setHours(0, 0, 0, 0)),
        value: value?.count,
        onClick: value?.onClick
      }
    });

    let refDate = startDate.setHours(0, 0, 0, 0);

    return Array(columnsCount).fill(0).map((_, index) => {

      const days = daysList.filter(x => x.date >= refDate).slice(0, index === 0 ? 7 - startDay : 7).filter(x => x != null);
      refDate = addDays(days[days.length - 1]?.date, 1).setHours(0, 0, 0, 0);

      const month = days.every(x => format(x.date, 'M') === format(days[0].date, 'M')) ?
        format(days[0].date, 'MMM', {
          locale: getLocale()
        }) : '';
      const year = format(refDate, 'y');

      return {
        index,
        month,
        year,
        days
      }
    });
  };

  const [columns] = useState(getColumns());
  const [legend] = useState([
    {
      color: '#EBEDF0',
      value: '= 0'
    },
    {
      color: legendColors && legendColors[0] ? legendColors[0] : '#9BE9A8',
      value: '= 1'
    },
    {
      color: legendColors && legendColors[1] ? legendColors[1] : '#40C463',
      value: '= 2'
    },
    {
      color: legendColors && legendColors[2] ? legendColors[2] : '#30A14E',
      value: '= 3'
    },
    {
      color: legendColors && legendColors[3] ? legendColors[3] : '#216E39',
      value: '>= 4'
    },
  ]);

  const showMonth = (index, month, year) => columns.find(x => x.month === month && x.year === year)?.index === index;

  const getBoxColor = (value) => {
    if (!value || value <= 0) return legend[0].color;
    else if (value === 1) return legend[1].color;
    else if (value === 2) return legend[2].color;
    else if (value === 3) return legend[3].color;
    else return legend[4].color;
  };

  return (
    <Container>
      <FlexContainer>
        <WeekContainer>
          {
            Array(7).fill(0).map((_, index) => (
              <WeekLabel style={{ visibility: showWeekDays.includes(index) ? 'visible' : 'hidden' }}>
                {getLocale().localize.day(index, { width: 'short' })}
              </WeekLabel>
            ))
          }
        </WeekContainer>
        <ColumnsContainer>
          {
            columns && columns.map((column) => {
              const { index, month, year, days } = column;

              return (
                <Column
                  {...column}>
                  <span style={{ left: index * 14, visibility: showMonths && showMonth(index, month, year) ? 'visible' : 'hidden' }}>
                    {month}
                  </span>
                  <BoxContainer>
                    {
                      days && days.map((day, indexDay) => {
                        const startDay = getStartDay();
                        const formulaMargin = startDay * 14;
                        const margin = startDay > 0 ? formulaMargin + 2 : formulaMargin;
                        return (
                          <Box
                            {...day}
                            color={getBoxColor(day.value)}
                            showTooltip={showTooltip}
                            boxShape={boxShape}
                            marginTop={index === 0 && indexDay === 0 ? margin || 2 : 2} />
                        );
                      })
                    }
                  </BoxContainer>
                </Column>
              );
            })
          }
        </ColumnsContainer>
      </FlexContainer>
      <FlexContainer legend>
        {
          contentBeforeLegend &&
          <span style={{ marginRight: 5 }}>{contentBeforeLegend}</span>
        }
        {
          legend && legend.map((legend) => (
            <Box {...legend} showTooltip boxShape={boxShape} />
          ))
        }
        {
          contentAfterLegend &&
          <span style={{ marginLeft: 5 }}>{contentAfterLegend}</span>
        }
      </FlexContainer>
    </Container>
  )
}

export default Heatmap;