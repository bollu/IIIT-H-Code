class AddSurveyIdToQuestion < ActiveRecord::Migration[5.0]
  def change
     add_reference :questions, :survey, foreign_key: true
     # TODO: got to check if this works or not
     #add_foreign_key :uploads, :users

  end
end
